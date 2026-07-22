package cn.edu.nju.Iot_Verify.component.nusmv;

import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.scheduling.annotation.Scheduled;
import org.springframework.stereotype.Component;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.time.Instant;
import java.util.Comparator;
import java.util.List;
import java.util.stream.Stream;

/** Bounds post-mortem NuSMV artifacts by age and directory count. */
@Slf4j
@Component
@RequiredArgsConstructor
public class NusmvTempArtifactCleaner {

    private static final String PREFIX = "nusmv_";
    private static final String LOCK_PREFIX = "." + PREFIX;
    private static final String LOCK_SUFFIX = ".active.lock";
    private static final Duration ACTIVE_GRACE = Duration.ofMinutes(10);

    private final NusmvConfig config;
    private final NusmvTempArtifactRegistry artifactRegistry;

    @Scheduled(fixedDelayString = "${nusmv.temp-cleanup-ms:300000}")
    public void cleanup() {
        Path tempRoot = Path.of(System.getProperty("java.io.tmpdir")).toAbsolutePath().normalize();
        cleanupRoot(tempRoot, Instant.now());
    }

    void cleanupRoot(Path root, Instant now) {
        Path tempRoot = root.toAbsolutePath().normalize();
        try (Stream<Path> entries = Files.list(tempRoot)) {
            List<Path> allEntries = entries.toList();
            List<Path> directories = allEntries.stream()
                    .filter(Files::isDirectory)
                    .filter(path -> path.getFileName().toString().startsWith(PREFIX))
                    .sorted(Comparator.comparing(this::lastModified))
                    .toList();
            Instant expiredBefore = now.minus(Duration.ofHours(config.getTempRetentionHours()));
            int retained = directories.size();
            for (Path directory : directories) {
                Instant modified = lastModified(directory);
                boolean expired = modified.isBefore(expiredBefore);
                boolean overCount = retained > config.getMaxRetainedTempDirectories()
                        && modified.isBefore(now.minus(ACTIVE_GRACE));
                if (!expired && !overCount) continue;
                if (artifactRegistry.deleteIfInactive(
                        directory, () -> deleteRecursively(tempRoot, directory))) {
                    retained--;
                }
            }
            cleanupOrphanMarkers(tempRoot, allEntries);
        } catch (IOException e) {
            log.warn("Could not enumerate NuSMV temporary artifacts: {}", e.getMessage());
        }
    }

    private void cleanupOrphanMarkers(Path tempRoot, List<Path> entries) {
        for (Path marker : entries) {
            String name = marker.getFileName().toString();
            if (!name.startsWith(LOCK_PREFIX) || !name.endsWith(LOCK_SUFFIX)) continue;
            String directoryName = name.substring(1, name.length() - LOCK_SUFFIX.length());
            if (!directoryName.startsWith(PREFIX)) continue;
            Path directory = tempRoot.resolve(directoryName).toAbsolutePath().normalize();
            if (Files.exists(directory)) continue;
            artifactRegistry.deleteIfInactive(directory, () -> !Files.exists(directory));
        }
    }

    private Instant lastModified(Path path) {
        try {
            return Files.getLastModifiedTime(path).toInstant();
        } catch (IOException e) {
            return Instant.EPOCH;
        }
    }

    private boolean deleteRecursively(Path tempRoot, Path directory) {
        Path target = directory.toAbsolutePath().normalize();
        if (!target.startsWith(tempRoot) || target.equals(tempRoot)
                || !target.getFileName().toString().startsWith(PREFIX)) {
            log.error("Refused unsafe NuSMV artifact cleanup target: {}", target);
            return false;
        }
        try (Stream<Path> paths = Files.walk(target)) {
            for (Path path : paths.sorted(Comparator.reverseOrder()).toList()) {
                Files.deleteIfExists(path);
            }
            log.debug("Deleted retained NuSMV artifact directory {}", target.getFileName());
            return true;
        } catch (IOException e) {
            log.warn("Could not delete NuSMV artifact directory {}: {}", target, e.getMessage());
            return false;
        }
    }
}
