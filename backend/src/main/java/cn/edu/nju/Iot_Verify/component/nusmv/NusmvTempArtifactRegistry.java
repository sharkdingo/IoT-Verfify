package cn.edu.nju.Iot_Verify.component.nusmv;

import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.io.File;
import java.io.IOException;
import java.nio.channels.FileChannel;
import java.nio.channels.FileLock;
import java.nio.channels.OverlappingFileLockException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.StandardOpenOption;
import java.util.HashMap;
import java.util.Map;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.BooleanSupplier;

/** Tracks active NuSMV directories and exposes an OS lock to other backend processes. */
@Slf4j
@Component
public class NusmvTempArtifactRegistry {

    private static final String LOCK_SUFFIX = ".active.lock";

    private final Map<Path, ActiveEntry> active = new HashMap<>();

    public synchronized ArtifactLease activate(File modelFile) {
        if (modelFile == null || modelFile.getParentFile() == null) {
            return new ArtifactLease(this, null);
        }
        Path directory = modelFile.getParentFile().toPath().toAbsolutePath().normalize();
        ActiveEntry existing = active.get(directory);
        if (existing != null) {
            existing.references++;
            return new ArtifactLease(this, directory);
        }

        FileChannel channel = null;
        FileLock lock = null;
        try {
            channel = FileChannel.open(lockPath(directory),
                    StandardOpenOption.CREATE, StandardOpenOption.WRITE);
            lock = channel.tryLock();
            if (lock == null) {
                closeQuietly(null, channel);
                throw new IllegalStateException(
                        "NuSMV artifact directory is being used or cleaned by another process: " + directory);
            }
        } catch (IOException | OverlappingFileLockException e) {
            closeQuietly(lock, channel);
            throw new IllegalStateException(
                    "Could not acquire the NuSMV artifact activity lock for " + directory, e);
        }
        active.put(directory, new ActiveEntry(channel, lock));
        return new ArtifactLease(this, directory);
    }

    public synchronized boolean isProtected(Path directory) {
        Path normalized = directory.toAbsolutePath().normalize();
        if (active.containsKey(normalized)) return true;
        Path marker = lockPath(normalized);
        if (!Files.exists(marker)) return false;

        try (FileChannel channel = FileChannel.open(marker, StandardOpenOption.WRITE)) {
            try (FileLock lock = channel.tryLock()) {
                return lock == null;
            } catch (OverlappingFileLockException e) {
                return true;
            }
        } catch (IOException e) {
            log.warn("Could not inspect NuSMV artifact activity lock {}: {}", marker, e.toString());
            return true;
        }
    }

    /** Holds the same local/OS exclusion from the activity check through recursive deletion. */
    public synchronized boolean deleteIfInactive(Path directory, BooleanSupplier deletion) {
        Path normalized = directory.toAbsolutePath().normalize();
        if (active.containsKey(normalized)) return false;

        Path marker = lockPath(normalized);
        FileChannel channel = null;
        FileLock lock = null;
        boolean deleted = false;
        try {
            channel = FileChannel.open(marker, StandardOpenOption.CREATE, StandardOpenOption.WRITE);
            lock = channel.tryLock();
            if (lock == null) return false;
            deleted = deletion.getAsBoolean();
            return deleted;
        } catch (IOException | OverlappingFileLockException e) {
            log.warn("Could not lock NuSMV artifact directory for cleanup {}: {}", normalized, e.toString());
            return false;
        } finally {
            closeQuietly(lock, channel);
            if (deleted) {
                try {
                    Files.deleteIfExists(marker);
                } catch (IOException e) {
                    log.debug("Could not remove released NuSMV artifact lock {}: {}", marker, e.toString());
                }
            }
        }
    }

    private static Path lockPath(Path directory) {
        Path fileName = directory.getFileName();
        if (fileName == null || directory.getParent() == null) {
            return directory.resolveSibling("nusmv-artifact" + LOCK_SUFFIX);
        }
        return directory.resolveSibling("." + fileName + LOCK_SUFFIX);
    }

    private synchronized void release(Path directory) {
        if (directory == null) return;
        ActiveEntry entry = active.get(directory);
        if (entry == null) return;
        entry.references--;
        if (entry.references > 0) return;
        active.remove(directory);
        closeQuietly(entry.lock, entry.channel);
    }

    private static void closeQuietly(FileLock lock, FileChannel channel) {
        if (lock != null) {
            try {
                lock.release();
            } catch (IOException ignored) {
            }
        }
        if (channel != null) {
            try {
                channel.close();
            } catch (IOException ignored) {
            }
        }
    }

    private static final class ActiveEntry {
        private final FileChannel channel;
        private final FileLock lock;
        private int references = 1;

        private ActiveEntry(FileChannel channel, FileLock lock) {
            this.channel = channel;
            this.lock = lock;
        }
    }

    public static final class ArtifactLease implements AutoCloseable {
        private final NusmvTempArtifactRegistry registry;
        private final Path directory;
        private final AtomicBoolean closed = new AtomicBoolean();

        private ArtifactLease(NusmvTempArtifactRegistry registry, Path directory) {
            this.registry = registry;
            this.directory = directory;
        }

        @Override
        public void close() {
            if (closed.compareAndSet(false, true)) {
                registry.release(directory);
            }
        }
    }
}
