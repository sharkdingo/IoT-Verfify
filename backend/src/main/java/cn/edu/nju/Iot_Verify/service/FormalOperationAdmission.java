package cn.edu.nju.Iot_Verify.service;

import org.springframework.stereotype.Component;
import org.springframework.transaction.support.TransactionSynchronization;
import org.springframework.transaction.support.TransactionSynchronizationManager;

import java.util.Objects;
import java.util.function.Supplier;

/** Single admission boundary for synchronous verification, simulation, and fix work. */
@Component
public class FormalOperationAdmission {

    private final UserOperationGuard userOperationGuard;
    private final FormalOperationFence formalOperationFence;
    private final ThreadLocal<CurrentAdmission> currentAdmission = new ThreadLocal<>();

    public FormalOperationAdmission(
            UserOperationGuard userOperationGuard, FormalOperationFence formalOperationFence) {
        this.userOperationGuard = Objects.requireNonNull(userOperationGuard, "userOperationGuard");
        this.formalOperationFence = Objects.requireNonNull(formalOperationFence, "formalOperationFence");
    }

    public <T> T execute(Long userId, Supplier<T> operation) {
        Objects.requireNonNull(operation, "operation must not be null");
        var lease = userOperationGuard.acquire(
                userId, UserOperationGuard.Kind.FORMAL, 1, userOperationGuard.renewableLeaseTtl());
        boolean closeImmediately = true;
        try {
            long fenceEpoch = formalOperationFence.claim(userId);
            CurrentAdmission previousAdmission = currentAdmission.get();
            currentAdmission.set(new CurrentAdmission(userId, fenceEpoch, lease));
            try {
                lease.requireActive();
                T result = operation.get();
                lease.requireActive();
                return result;
            } finally {
                if (previousAdmission == null) {
                    currentAdmission.remove();
                } else {
                    currentAdmission.set(previousAdmission);
                }
            }
        } finally {
            try {
                if (TransactionSynchronizationManager.isActualTransactionActive()
                        && TransactionSynchronizationManager.isSynchronizationActive()) {
                    TransactionSynchronizationManager.registerSynchronization(new TransactionSynchronization() {
                        @Override
                        public void afterCompletion(int status) {
                            lease.close();
                        }
                    });
                    closeImmediately = false;
                }
            } finally {
                if (closeImmediately) {
                    lease.close();
                }
            }
        }
    }

    /** Fails the current transaction before commit if its owning formal-operation lease is lost. */
    public void registerCurrentLeaseCommitFence() {
        CurrentAdmission admission = currentAdmission.get();
        if (admission == null) {
            return;
        }
        if (!TransactionSynchronizationManager.isActualTransactionActive()
                || !TransactionSynchronizationManager.isSynchronizationActive()) {
            throw new IllegalStateException(
                    "A formal-operation commit fence requires an active Spring transaction");
        }
        admission.lease().requireActive();
        TransactionSynchronizationManager.registerSynchronization(new TransactionSynchronization() {
            @Override
            public void beforeCommit(boolean readOnly) {
                formalOperationFence.lockAndRequireCurrent(
                        admission.userId(), admission.fenceEpoch());
                admission.lease().requireActive();
            }
        });
    }

    private record CurrentAdmission(
            Long userId, long fenceEpoch, UserOperationGuard.Lease lease) {
    }
}
