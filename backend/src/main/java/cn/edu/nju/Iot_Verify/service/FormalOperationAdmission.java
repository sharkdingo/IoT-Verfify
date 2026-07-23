package cn.edu.nju.Iot_Verify.service;

import lombok.RequiredArgsConstructor;
import org.springframework.stereotype.Component;
import org.springframework.transaction.support.TransactionSynchronization;
import org.springframework.transaction.support.TransactionSynchronizationManager;

import java.util.Objects;
import java.util.function.Supplier;

/** Single admission boundary for synchronous verification, simulation, and fix work. */
@Component
@RequiredArgsConstructor
public class FormalOperationAdmission {

    private final UserOperationGuard userOperationGuard;
    private final ThreadLocal<UserOperationGuard.Lease> currentLease = new ThreadLocal<>();

    public <T> T execute(Long userId, Supplier<T> operation) {
        Objects.requireNonNull(operation, "operation must not be null");
        try (var lease = userOperationGuard.acquire(
                userId, UserOperationGuard.Kind.FORMAL, 1, userOperationGuard.renewableLeaseTtl())) {
            UserOperationGuard.Lease previousLease = currentLease.get();
            currentLease.set(lease);
            try {
                lease.requireActive();
                T result = operation.get();
                lease.requireActive();
                return result;
            } finally {
                if (previousLease == null) {
                    currentLease.remove();
                } else {
                    currentLease.set(previousLease);
                }
            }
        }
    }

    /** Fails the current transaction before commit if its owning formal-operation lease is lost. */
    public void registerCurrentLeaseCommitFence() {
        UserOperationGuard.Lease lease = currentLease.get();
        if (lease == null) {
            return;
        }
        if (!TransactionSynchronizationManager.isActualTransactionActive()
                || !TransactionSynchronizationManager.isSynchronizationActive()) {
            throw new IllegalStateException(
                    "A formal-operation commit fence requires an active Spring transaction");
        }
        lease.requireActive();
        TransactionSynchronizationManager.registerSynchronization(new TransactionSynchronization() {
            @Override
            public void beforeCommit(boolean readOnly) {
                lease.requireActive();
            }
        });
    }
}
