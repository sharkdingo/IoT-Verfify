package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.po.TaskView;
import org.junit.jupiter.api.Test;
import org.springframework.transaction.PlatformTransactionManager;
import org.springframework.transaction.TransactionDefinition;
import org.springframework.transaction.TransactionStatus;
import org.springframework.transaction.support.SimpleTransactionStatus;
import org.springframework.transaction.support.TransactionTemplate;

import java.time.Duration;
import java.time.LocalDateTime;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class TaskLeaseRenewalTest {

    @Test
    void lockWaitThatCrossesExpiryCannotRenewOrConfirmLease() {
        LocalDateTime beforeLock = LocalDateTime.of(2026, 7, 23, 10, 0);
        LocalDateTime afterLock = beforeLock.plusSeconds(2);
        TestTask task = new TestTask("worker-a", "RUNNING", beforeLock.plusSeconds(1));
        AtomicReference<LocalDateTime> databaseTime = new AtomicReference<>(beforeLock);
        AtomicBoolean flushed = new AtomicBoolean();

        boolean renewed = TaskLeaseRenewal.renew(
                transactionTemplate(),
                () -> {
                    databaseTime.set(afterLock);
                    return Optional.of(task);
                },
                databaseTime::get,
                ignored -> flushed.set(true),
                "worker-a",
                Duration.ofMinutes(2));

        assertFalse(renewed);
        assertFalse(flushed.get());
        assertEquals(beforeLock.plusSeconds(1), task.getLeaseExpiresAt());
    }

    @Test
    void ownedActiveLeaseUsesDatabaseTimeSampledAfterLock() {
        LocalDateTime afterLock = LocalDateTime.of(2026, 7, 23, 10, 0, 5);
        TestTask task = new TestTask("worker-a", "PENDING", afterLock.plusSeconds(10));
        AtomicBoolean lockAcquired = new AtomicBoolean();
        AtomicBoolean flushed = new AtomicBoolean();

        boolean renewed = TaskLeaseRenewal.renew(
                transactionTemplate(),
                () -> {
                    lockAcquired.set(true);
                    return Optional.of(task);
                },
                () -> {
                    assertTrue(lockAcquired.get());
                    return afterLock;
                },
                ignored -> flushed.set(true),
                "worker-a",
                Duration.ofMinutes(2));

        assertTrue(renewed);
        assertTrue(flushed.get());
        assertEquals(afterLock.plusMinutes(2), task.getLeaseExpiresAt());
    }

    private TransactionTemplate transactionTemplate() {
        return new TransactionTemplate(new PlatformTransactionManager() {
            @Override
            public TransactionStatus getTransaction(TransactionDefinition definition) {
                return new SimpleTransactionStatus();
            }

            @Override
            public void commit(TransactionStatus status) {
            }

            @Override
            public void rollback(TransactionStatus status) {
            }
        });
    }

    private static final class TestTask implements TaskView {
        private final String workerId;
        private final String status;
        private LocalDateTime leaseExpiresAt;

        private TestTask(String workerId, String status, LocalDateTime leaseExpiresAt) {
            this.workerId = workerId;
            this.status = status;
            this.leaseExpiresAt = leaseExpiresAt;
        }

        @Override public Long getId() { return 1L; }
        @Override public Integer getProgress() { return 0; }
        @Override public boolean isTerminalStatus() { return false; }
        @Override public boolean isCancelledStatus() { return false; }
        @Override public String getTaskStatusName() { return status; }
        @Override public String getCheckLogsJson() { return "[]"; }
        @Override public void setCheckLogsJson(String json) { }
        @Override public String getWorkerId() { return workerId; }
        @Override public LocalDateTime getLeaseExpiresAt() { return leaseExpiresAt; }
        @Override public void setLeaseExpiresAt(LocalDateTime value) { leaseExpiresAt = value; }
    }
}
