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
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

class FormalOperationAdmissionTest {

    @Test
    void executeOwnsAndChecksFormalLeaseAroundOperation() {
        UserOperationGuard guard = mock(UserOperationGuard.class);
        UserOperationGuard.Lease lease = mock(UserOperationGuard.Lease.class);
        when(guard.renewableLeaseTtl()).thenReturn(Duration.ofMinutes(2));
        when(guard.acquire(7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(2)))
                .thenReturn(lease);
        AtomicBoolean invoked = new AtomicBoolean();

        String result = new FormalOperationAdmission(guard).execute(7L, () -> {
            invoked.set(true);
            return "done";
        });

        assertEquals("done", result);
        assertTrue(invoked.get());
        verify(lease, times(2)).requireActive();
        verify(lease).close();
        verify(guard).acquire(7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(2));
    }

    @Test
    void commitFenceRollsBackWhenLeaseIsLostBeforeCommit() {
        UserOperationGuard guard = mock(UserOperationGuard.class);
        UserOperationGuard.Lease lease = mock(UserOperationGuard.Lease.class);
        when(guard.renewableLeaseTtl()).thenReturn(Duration.ofMinutes(2));
        when(guard.acquire(7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(2)))
                .thenReturn(lease);
        ServiceUnavailableException leaseLost = new ServiceUnavailableException("lease lost");
        doNothing().doNothing().doThrow(leaseLost).when(lease).requireActive();
        RecordingTransactionManager transactionManager = new RecordingTransactionManager();
        TransactionTemplate transactionTemplate = new TransactionTemplate(transactionManager);
        FormalOperationAdmission admission = new FormalOperationAdmission(guard);
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
        verify(lease).close();
    }

    @Test
    void commitFenceIsNoOpOutsideFormalOperation() {
        UserOperationGuard guard = mock(UserOperationGuard.class);
        RecordingTransactionManager transactionManager = new RecordingTransactionManager();
        TransactionTemplate transactionTemplate = new TransactionTemplate(transactionManager);
        FormalOperationAdmission admission = new FormalOperationAdmission(guard);

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
