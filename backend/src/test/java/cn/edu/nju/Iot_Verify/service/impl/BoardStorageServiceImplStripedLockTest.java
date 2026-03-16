package cn.edu.nju.Iot_Verify.service.impl;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Method;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for striped lock implementation in BoardStorageServiceImpl.
 * Verifies the lock mapping logic without requiring full service integration.
 */
class BoardStorageServiceImplStripedLockTest {

    @Test
    @DisplayName("Striped lock: same userId always maps to same lock object")
    void sameUserId_sameStripe() throws Exception {
        BoardStorageServiceImpl service = createMinimalService();
        Method getLock = BoardStorageServiceImpl.class.getDeclaredMethod("getUserWriteLock", Long.class);
        getLock.setAccessible(true);

        Long userId = 42L;
        Object lock1 = getLock.invoke(service, userId);
        Object lock2 = getLock.invoke(service, userId);

        assertSame(lock1, lock2, "Same userId should always return the same lock object");
    }

    @Test
    @DisplayName("Striped lock: hash collision maps to same stripe")
    void hashCollision_sameStripe() throws Exception {
        BoardStorageServiceImpl service = createMinimalService();
        Method getLock = BoardStorageServiceImpl.class.getDeclaredMethod("getUserWriteLock", Long.class);
        getLock.setAccessible(true);

        // userId1 and userId2 map to same stripe (userId % 1024)
        Long userId1 = 1L;
        Long userId2 = 1025L; // 1025 % 1024 = 1

        Object lock1 = getLock.invoke(service, userId1);
        Object lock2 = getLock.invoke(service, userId2);

        assertSame(lock1, lock2, "Hash collision should map to the same lock stripe");
    }

    @Test
    @DisplayName("Striped lock: different userIds without collision map to different stripes")
    void differentUserId_differentStripe() throws Exception {
        BoardStorageServiceImpl service = createMinimalService();
        Method getLock = BoardStorageServiceImpl.class.getDeclaredMethod("getUserWriteLock", Long.class);
        getLock.setAccessible(true);

        Long userId1 = 1L;
        Long userId2 = 2L;

        Object lock1 = getLock.invoke(service, userId1);
        Object lock2 = getLock.invoke(service, userId2);

        assertNotSame(lock1, lock2, "Different userIds (no collision) should map to different lock stripes");
    }

    @Test
    @DisplayName("Striped lock: array has exactly 1024 stripes")
    void stripedLock_has1024Stripes() throws Exception {
        BoardStorageServiceImpl service = createMinimalService();
        Field locksField = BoardStorageServiceImpl.class.getDeclaredField("userWriteLocks");
        locksField.setAccessible(true);

        Object[] locks = (Object[]) locksField.get(service);

        assertEquals(1024, locks.length, "Lock array should have exactly 1024 stripes");
        for (int i = 0; i < locks.length; i++) {
            assertNotNull(locks[i], "Lock stripe " + i + " should be initialized");
        }
    }

    @Test
    @DisplayName("Striped lock: modulo mapping is deterministic")
    void stripedLock_deterministicMapping() throws Exception {
        BoardStorageServiceImpl service = createMinimalService();
        Method getLock = BoardStorageServiceImpl.class.getDeclaredMethod("getUserWriteLock", Long.class);
        getLock.setAccessible(true);

        // Test multiple userIds to verify deterministic mapping
        for (long userId = 0; userId < 10000; userId += 100) {
            Object lock1 = getLock.invoke(service, userId);
            Object lock2 = getLock.invoke(service, userId);
            assertSame(lock1, lock2, "userId " + userId + " should always map to the same lock");
        }
    }

    /**
     * Create a minimal BoardStorageServiceImpl instance for testing lock logic only.
     * All dependencies are null since we only test getUserWriteLock().
     */
    private BoardStorageServiceImpl createMinimalService() {
        return new BoardStorageServiceImpl(
                null, null, null, null, null, null, null, null, null,
                null, null, null, null, null, null, null, null
        );
    }
}
