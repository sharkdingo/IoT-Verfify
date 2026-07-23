package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import org.junit.jupiter.api.Test;
import org.springframework.transaction.TransactionDefinition;
import org.springframework.transaction.support.AbstractPlatformTransactionManager;
import org.springframework.transaction.support.DefaultTransactionStatus;
import org.springframework.transaction.support.TransactionTemplate;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

class FormalOperationFenceTest {

    @Test
    void claimAtomicallyAdvancesThePersistedEpoch() {
        UserRepository users = mock(UserRepository.class);
        UserPo user = UserPo.builder().id(7L).formalOperationFence(4L).build();
        when(users.findByIdForUpdate(7L)).thenReturn(Optional.of(user));
        RecordingTransactionManager transactions = new RecordingTransactionManager();
        FormalOperationFence fence = new FormalOperationFence(users, transactions);

        long epoch = fence.claim(7L);

        assertEquals(5L, epoch);
        assertEquals(5L, user.getFormalOperationFence());
        assertEquals(1, transactions.commits);
        verify(users).findByIdForUpdate(7L);
    }

    @Test
    void lockedCommitCheckRejectsAnOlderEpoch() {
        UserRepository users = mock(UserRepository.class);
        UserPo user = UserPo.builder().id(7L).formalOperationFence(6L).build();
        when(users.findByIdForUpdate(7L)).thenReturn(Optional.of(user));
        RecordingTransactionManager transactions = new RecordingTransactionManager();
        FormalOperationFence fence = new FormalOperationFence(users, transactions);
        TransactionTemplate transaction = new TransactionTemplate(transactions);

        assertThrows(ServiceUnavailableException.class,
                () -> transaction.executeWithoutResult(status ->
                        fence.lockAndRequireCurrent(7L, 5L)));

        verify(users, times(1)).findByIdForUpdate(7L);
        assertEquals(1, transactions.rollbacks);
    }

    private static final class RecordingTransactionManager extends AbstractPlatformTransactionManager {
        private int commits;
        private int rollbacks;

        @Override
        protected Object doGetTransaction() {
            return new Object();
        }

        @Override
        protected void doBegin(Object transaction, TransactionDefinition definition) {
        }

        @Override
        protected void doCommit(DefaultTransactionStatus status) {
            commits++;
        }

        @Override
        protected void doRollback(DefaultTransactionStatus status) {
            rollbacks++;
        }
    }
}
