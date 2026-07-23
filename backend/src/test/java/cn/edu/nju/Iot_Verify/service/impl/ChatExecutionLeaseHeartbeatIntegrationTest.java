package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.ai.AiTaskContinuationStore;
import cn.edu.nju.Iot_Verify.component.ai.ChatConfirmationDetector;
import cn.edu.nju.Iot_Verify.component.ai.LlmChatService;
import cn.edu.nju.Iot_Verify.component.ai.LlmMessageCodec;
import cn.edu.nju.Iot_Verify.component.aitool.AiDestructiveActionGuard;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolManager;
import cn.edu.nju.Iot_Verify.component.aitool.scenario.AiScenarioDraftStore;
import cn.edu.nju.Iot_Verify.configure.ChatExecutionConfig;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.repository.ChatMessageRepository;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.util.mapper.ChatMapper;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.jdbc.AutoConfigureTestDatabase;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;
import org.springframework.transaction.PlatformTransactionManager;
import org.springframework.transaction.annotation.Propagation;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.transaction.support.TransactionTemplate;

import java.time.Duration;
import java.util.Optional;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.Future;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.LockSupport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.AdditionalAnswers.delegatesTo;
import static org.mockito.Mockito.doAnswer;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@DataJpaTest(properties = {
        "spring.jpa.database-platform=org.hibernate.dialect.H2Dialect",
        "spring.jpa.properties.hibernate.dialect=org.hibernate.dialect.H2Dialect",
        "spring.jpa.hibernate.ddl-auto=create-drop"
})
@AutoConfigureTestDatabase(replace = AutoConfigureTestDatabase.Replace.ANY)
@Transactional(propagation = Propagation.NOT_SUPPORTED)
class ChatExecutionLeaseHeartbeatIntegrationTest {

    @Autowired
    private ChatSessionRepository repository;

    @Autowired
    private PlatformTransactionManager transactionManager;

    @Test
    void heartbeatDoesNotRenewWithStaleTimeAfterRowLockWaitExceedsTtl() throws Exception {
        ChatSessionRepository observedRepository = mock(
                ChatSessionRepository.class, delegatesTo(repository));
        ChatServiceImpl service = service(observedRepository);
        ChatSessionPo session = new ChatSessionPo();
        session.setId("locked-session");
        session.setUserId(1L);
        session.setExecutionStopRequested(false);
        session.setExecutionUserStopRequested(false);
        new TransactionTemplate(transactionManager).executeWithoutResult(
                status -> repository.saveAndFlush(session));
        service.beginStreamRequest(1L, "locked-session");

        CountDownLatch rowLocked = new CountDownLatch(1);
        CountDownLatch heartbeatWaitingForLock = new CountDownLatch(1);
        CountDownLatch releaseRow = new CountDownLatch(1);
        ExecutorService executor = Executors.newFixedThreadPool(2);
        Future<?> lockHolder = executor.submit(() -> new TransactionTemplate(transactionManager)
                .executeWithoutResult(status -> {
                    repository.findByIdAndUserIdForUpdate("locked-session", 1L).orElseThrow();
                    rowLocked.countDown();
                    await(releaseRow);
                }));

        try {
            assertTrue(rowLocked.await(2, TimeUnit.SECONDS));
            doAnswer(invocation -> {
                heartbeatWaitingForLock.countDown();
                return repository.findByIdAndUserIdForUpdate("locked-session", 1L);
            }).when(observedRepository).findByIdAndUserIdForUpdate("locked-session", 1L);
            Future<?> heartbeat = executor.submit(service::maintainExecutionLeases);

            assertTrue(heartbeatWaitingForLock.await(2, TimeUnit.SECONDS));
            LockSupport.parkNanos(Duration.ofMillis(150).toNanos());
            releaseRow.countDown();
            heartbeat.get(2, TimeUnit.SECONDS);

            verify(observedRepository, times(1)).saveAndFlush(session);
            assertFalse(service.getSessionActivity(1L, "locked-session").isActive());
            ChatSessionPo expired = repository.findById("locked-session").orElseThrow();
            assertNull(expired.getActiveExecutionId());
            assertNull(expired.getActiveExecutionExpiresAt());
        } finally {
            releaseRow.countDown();
            lockHolder.get(2, TimeUnit.SECONDS);
            executor.shutdownNow();
        }
    }

    private ChatServiceImpl service(ChatSessionRepository observedRepository) {
        UserRepository userRepository = mock(UserRepository.class);
        when(userRepository.findByIdForUpdate(1L))
                .thenReturn(Optional.of(UserPo.builder().id(1L).build()));
        ObjectMapper objectMapper = new ObjectMapper();
        ChatExecutionConfig config = new ChatExecutionConfig();
        config.setLeaseTtlMs(50);
        config.setLeaseHeartbeatMs(10);
        return new ChatServiceImpl(
                observedRepository,
                mock(ChatMessageRepository.class),
                userRepository,
                mock(LlmChatService.class),
                new LlmMessageCodec(objectMapper),
                mock(ChatConfirmationDetector.class),
                mock(AiToolManager.class),
                mock(AiDestructiveActionGuard.class),
                mock(AiScenarioDraftStore.class),
                mock(AiTaskContinuationStore.class),
                objectMapper,
                mock(ChatMapper.class),
                new TransactionTemplate(transactionManager),
                config);
    }

    private void await(CountDownLatch latch) {
        try {
            if (!latch.await(5, TimeUnit.SECONDS)) {
                throw new IllegalStateException("Timed out waiting for test coordination");
            }
        } catch (InterruptedException e) {
            Thread.currentThread().interrupt();
            throw new IllegalStateException("Interrupted while coordinating test", e);
        }
    }
}
