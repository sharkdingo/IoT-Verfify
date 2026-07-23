package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import org.junit.jupiter.api.Test;
import org.springframework.transaction.TransactionDefinition;
import org.springframework.transaction.support.AbstractPlatformTransactionManager;
import org.springframework.transaction.support.DefaultTransactionStatus;
import org.springframework.transaction.support.TransactionTemplate;

import java.time.Duration;
import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.doNothing;
import static org.mockito.Mockito.doAnswer;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

class FormalOperationAdmissionTest {

    @Test
    void executeOwnsAndChecksFormalLeaseAroundOperation() {
        UserOperationGuard guard = mock(UserOperationGuard.class);
        FormalOperationFence fence = mock(FormalOperationFence.class);
        UserOperationGuard.Lease lease = mock(UserOperationGuard.Lease.class);
        when(guard.renewableLeaseTtl()).thenReturn(Duration.ofMinutes(2));
        when(guard.acquire(7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(2)))
                .thenReturn(lease);
        when(fence.claim(7L)).thenReturn(11L);
        AtomicBoolean invoked = new AtomicBoolean();

        String result = new FormalOperationAdmission(guard, fence).execute(7L, () -> {
            invoked.set(true);
            return "done";
        });

        assertEquals("done", result);
        assertTrue(invoked.get());
        verify(lease, times(2)).requireActive();
        verify(lease).close();
        verify(guard).acquire(7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(2));
        verify(fence).claim(7L);
    }

    @Test
    void commitFenceRollsBackWhenLeaseIsLostBeforeCommit() {
        UserOperationGuard guard = mock(UserOperationGuard.class);
        FormalOperationFence fence = mock(FormalOperationFence.class);
        UserOperationGuard.Lease lease = mock(UserOperationGuard.Lease.class);
        when(guard.renewableLeaseTtl()).thenReturn(Duration.ofMinutes(2));
        when(guard.acquire(7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(2)))
                .thenReturn(lease);
        when(fence.claim(7L)).thenReturn(11L);
        ServiceUnavailableException leaseLost = new ServiceUnavailableException("lease lost");
        doNothing().doNothing().doThrow(leaseLost).when(lease).requireActive();
        RecordingTransactionManager transactionManager = new RecordingTransactionManager();
        TransactionTemplate transactionTemplate = new TransactionTemplate(transactionManager);
        FormalOperationAdmission admission = new FormalOperationAdmission(guard, fence);
        AtomicBoolean workExecuted = new AtomicBoolean();

        ServiceUnavailableException error = assertThrows(ServiceUnavailableException.class,
                () -> admission.execute(7L, () -> transactionTemplate.execute(status -> {
                    admission.registerCurrentLeaseCommitFence();
                    workExecuted.set(true);
                    return "saved";
                })));

        assertEquals(leaseLost, error);
        assertTrue(workExecuted.get());
        assertFalse(transactionManager.committed);
        assertTrue(transactionManager.rolledBack);
        verify(lease, times(3)).requireActive();
        verify(fence).lockAndRequireCurrent(7L, 11L);
        verify(lease).close();
    }

    @Test
    void ambientTransactionKeepsLeaseUntilCommitFenceAndCompletion() {
        UserOperationGuard guard = mock(UserOperationGuard.class);
        FormalOperationFence fence = mock(FormalOperationFence.class);
        UserOperationGuard.Lease lease = mock(UserOperationGuard.Lease.class);
        when(guard.renewableLeaseTtl()).thenReturn(Duration.ofMinutes(2));
        when(guard.acquire(7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(2)))
                .thenReturn(lease);
        when(fence.claim(7L)).thenReturn(11L);
        AtomicBoolean closed = new AtomicBoolean();
        ServiceUnavailableException closedLease = new ServiceUnavailableException("lease closed before commit");
        doAnswer(invocation -> {
            if (closed.get()) throw closedLease;
            return null;
        }).when(lease).requireActive();
        doAnswer(invocation -> {
            closed.set(true);
            return null;
        }).when(lease).close();
        RecordingTransactionManager transactionManager = new RecordingTransactionManager();
        TransactionTemplate transactionTemplate = new TransactionTemplate(transactionManager);
        FormalOperationAdmission admission = new FormalOperationAdmission(guard, fence);

        String result = transactionTemplate.execute(status -> {
            String value = admission.execute(7L, () -> {
                admission.registerCurrentLeaseCommitFence();
                return "saved";
            });
            assertFalse(closed.get(), "the ambient transaction has not committed yet");
            return value;
        });

        assertEquals("saved", result);
        assertTrue(transactionManager.committed);
        assertFalse(transactionManager.rolledBack);
        assertTrue(closed.get());
        verify(lease, times(4)).requireActive();
        verify(fence).lockAndRequireCurrent(7L, 11L);
        verify(lease).close();
    }

    @Test
    void commitFenceRollsBackWhenDatabaseEpochWasSuperseded() {
        UserOperationGuard guard = mock(UserOperationGuard.class);
        FormalOperationFence fence = mock(FormalOperationFence.class);
        UserOperationGuard.Lease lease = mock(UserOperationGuard.Lease.class);
        when(guard.renewableLeaseTtl()).thenReturn(Duration.ofMinutes(2));
        when(guard.acquire(7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(2)))
                .thenReturn(lease);
        when(fence.claim(7L)).thenReturn(11L);
        ServiceUnavailableException superseded =
                new ServiceUnavailableException("superseded");
        doThrow(superseded).when(fence).lockAndRequireCurrent(7L, 11L);
        RecordingTransactionManager transactionManager = new RecordingTransactionManager();
        TransactionTemplate transactionTemplate = new TransactionTemplate(transactionManager);
        FormalOperationAdmission admission = new FormalOperationAdmission(guard, fence);

        ServiceUnavailableException error = assertThrows(ServiceUnavailableException.class,
                () -> admission.execute(7L, () -> transactionTemplate.execute(status -> {
                    admission.registerCurrentLeaseCommitFence();
                    return "saved";
                })));

        assertEquals(superseded, error);
        assertFalse(transactionManager.committed);
        assertTrue(transactionManager.rolledBack);
        verify(lease, times(2)).requireActive();
        verify(lease).close();
    }

    @Test
    void commitFenceIsNoOpOutsideFormalOperation() {
        UserOperationGuard guard = mock(UserOperationGuard.class);
        FormalOperationFence fence = mock(FormalOperationFence.class);
        RecordingTransactionManager transactionManager = new RecordingTransactionManager();
        TransactionTemplate transactionTemplate = new TransactionTemplate(transactionManager);
        FormalOperationAdmission admission = new FormalOperationAdmission(guard, fence);

        transactionTemplate.executeWithoutResult(status ->
                admission.registerCurrentLeaseCommitFence());

        assertTrue(transactionManager.committed);
        assertFalse(transactionManager.rolledBack);
    }

    private static final class RecordingTransactionManager extends AbstractPlatformTransactionManager {
        private boolean committed;
        private boolean rolledBack;

        @Override
        protected Object doGetTransaction() {
            return new Object();
        }

        @Override
        protected void doBegin(Object transaction, TransactionDefinition definition) {
            // No resource is needed; AbstractPlatformTransactionManager still drives synchronization callbacks.
        }

        @Override
        protected void doCommit(DefaultTransactionStatus status) {
            committed = true;
        }

        @Override
        protected void doRollback(DefaultTransactionStatus status) {
            rolledBack = true;
        }
    }
}
