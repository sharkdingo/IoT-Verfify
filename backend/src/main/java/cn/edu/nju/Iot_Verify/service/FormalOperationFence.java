package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import org.springframework.stereotype.Component;
import org.springframework.transaction.PlatformTransactionManager;
import org.springframework.transaction.TransactionDefinition;
import org.springframework.transaction.support.TransactionSynchronizationManager;
import org.springframework.transaction.support.TransactionTemplate;

import java.util.Objects;

/** Database fencing epoch that prevents an expired formal-operation lease from committing. */
@Component
public final class FormalOperationFence {

    private final UserRepository userRepository;
    private final TransactionTemplate claimTransaction;

    public FormalOperationFence(
            UserRepository userRepository, PlatformTransactionManager transactionManager) {
        this.userRepository = Objects.requireNonNull(userRepository, "userRepository");
        claimTransaction = new TransactionTemplate(
                Objects.requireNonNull(transactionManager, "transactionManager"));
        claimTransaction.setPropagationBehavior(TransactionDefinition.PROPAGATION_REQUIRES_NEW);
    }

    /** Claims a new epoch before expensive work begins. */
    public long claim(Long userId) {
        Long requiredUserId = Objects.requireNonNull(userId, "userId");
        Long epoch = claimTransaction.execute(status -> {
            UserPo user = userRepository.findByIdForUpdate(requiredUserId)
                    .orElseThrow(() -> ResourceNotFoundException.user(requiredUserId));
            Long currentEpoch = user.getFormalOperationFence();
            if (currentEpoch == null || currentEpoch < 0) {
                throw new IllegalStateException("Formal-operation fencing epoch is invalid");
            }
            long next;
            try {
                next = Math.addExact(currentEpoch, 1L);
            } catch (ArithmeticException exception) {
                throw new IllegalStateException("Formal-operation fencing epoch is exhausted", exception);
            }
            user.setFormalOperationFence(next);
            return next;
        });
        return Objects.requireNonNull(epoch, "formal-operation fencing epoch");
    }

    /** Locks the epoch row through physical commit and rejects superseded work. */
    public void lockAndRequireCurrent(Long userId, long expectedEpoch) {
        if (!TransactionSynchronizationManager.isActualTransactionActive()) {
            throw new IllegalStateException("Formal-operation fencing requires an active transaction");
        }
        UserPo user = userRepository.findByIdForUpdate(userId)
                .orElseThrow(() -> ResourceNotFoundException.user(userId));
        if (!Objects.equals(user.getFormalOperationFence(), expectedEpoch)) {
            throw new ServiceUnavailableException(
                    "Formal operation ownership changed before commit; retry the operation");
        }
    }
}
