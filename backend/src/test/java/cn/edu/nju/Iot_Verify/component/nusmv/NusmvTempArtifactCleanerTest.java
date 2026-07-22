package cn.edu.nju.Iot_Verify.component.nusmv;

import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.attribute.FileTime;
import java.time.Instant;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.TimeoutException;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertThrows;

class NusmvTempArtifactCleanerTest {

    @TempDir
    Path tempRoot;

    @Test
    void activeArtifactIsRetainedUntilItsExecutionLeaseCloses() throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setTempRetentionHours(1);
        config.setMaxRetainedTempDirectories(1);
        NusmvTempArtifactRegistry registry = new NusmvTempArtifactRegistry();
        NusmvTempArtifactCleaner cleaner = new NusmvTempArtifactCleaner(config, registry);
        Path directory = Files.createDirectory(tempRoot.resolve("nusmv_verify_test"));
        Path model = Files.writeString(directory.resolve("model.smv"), "MODULE main\n");
        Instant now = Instant.parse("2026-07-22T00:00:00Z");
        Files.setLastModifiedTime(directory, FileTime.from(now.minusSeconds(7200)));

        try (var ignored = registry.activate(model.toFile())) {
            cleaner.cleanupRoot(tempRoot, now);
            assertTrue(Files.exists(directory));
        }

        cleaner.cleanupRoot(tempRoot, now);
        assertFalse(Files.exists(directory));
    }

    @Test
    void activationCannotInterleaveBetweenCleanupCheckAndDeletion() throws Exception {
        NusmvTempArtifactRegistry registry = new NusmvTempArtifactRegistry();
        Path directory = Files.createDirectory(tempRoot.resolve("nusmv_verify_race"));
        Path model = Files.writeString(directory.resolve("model.smv"), "MODULE main\n");
        CountDownLatch deletionStarted = new CountDownLatch(1);
        CountDownLatch allowDeletion = new CountDownLatch(1);

        CompletableFuture<Boolean> cleanup = CompletableFuture.supplyAsync(() ->
                registry.deleteIfInactive(directory, () -> {
                    deletionStarted.countDown();
                    try {
                        if (!allowDeletion.await(5, TimeUnit.SECONDS)) return false;
                        Files.deleteIfExists(model);
                        Files.deleteIfExists(directory);
                        return true;
                    } catch (Exception e) {
                        throw new RuntimeException(e);
                    }
                }));
        assertTrue(deletionStarted.await(5, TimeUnit.SECONDS));

        CompletableFuture<NusmvTempArtifactRegistry.ArtifactLease> activation =
                CompletableFuture.supplyAsync(() -> registry.activate(model.toFile()));
        assertThrows(TimeoutException.class, () -> activation.get(100, TimeUnit.MILLISECONDS));

        allowDeletion.countDown();
        assertTrue(cleanup.get(5, TimeUnit.SECONDS));
        try (var ignored = activation.get(5, TimeUnit.SECONDS)) {
            assertFalse(Files.exists(model));
        }
    }

    @Test
    void orphanActivityMarkerIsRemovedAfterItsDirectoryWasDeletedElsewhere() throws Exception {
        NusmvConfig config = new NusmvConfig();
        NusmvTempArtifactRegistry registry = new NusmvTempArtifactRegistry();
        NusmvTempArtifactCleaner cleaner = new NusmvTempArtifactCleaner(config, registry);
        Path directory = Files.createDirectory(tempRoot.resolve("nusmv_fix_orphan"));
        Path model = Files.writeString(directory.resolve("model.smv"), "MODULE main\n");
        Path marker = NusmvTempArtifactRegistry.lockPath(directory.toAbsolutePath().normalize());

        try (var ignored = registry.activate(model.toFile())) {
            assertTrue(Files.exists(marker));
        }
        Files.delete(model);
        Files.delete(directory);

        cleaner.cleanupRoot(tempRoot, Instant.now());

        assertFalse(Files.exists(marker));
    }
}
