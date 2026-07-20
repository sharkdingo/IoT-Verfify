package cn.edu.nju.Iot_Verify.component.ai.state;

import cn.edu.nju.Iot_Verify.repository.AiSessionStateRepository;
import cn.edu.nju.Iot_Verify.service.ChatExecutionLeaseGuard;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.JsonNodeFactory;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.jdbc.AutoConfigureTestDatabase;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;
import org.springframework.transaction.annotation.Propagation;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.transaction.support.TransactionSynchronization;
import org.springframework.transaction.support.TransactionSynchronizationManager;
import org.springframework.transaction.support.TransactionTemplate;

import java.time.Instant;
import java.util.concurrent.atomic.AtomicReference;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.mock;

@DataJpaTest(properties = {
        "spring.jpa.database-platform=org.hibernate.dialect.H2Dialect",
        "spring.jpa.properties.hibernate.dialect=org.hibernate.dialect.H2Dialect",
        "spring.jpa.hibernate.ddl-auto=create-drop"
})
@AutoConfigureTestDatabase(replace = AutoConfigureTestDatabase.Replace.ANY)
class JpaAiSessionStateStoreTest {

    @Autowired
    private AiSessionStateRepository repository;
    @Autowired
    private TransactionTemplate transactionTemplate;

    @Test
    void stateSurvivesStoreInstancesAndIsConsumedWithCompareAndDelete() {
        ChatExecutionLeaseGuard leaseGuard = mock(ChatExecutionLeaseGuard.class);
        JpaAiSessionStateStore writer = new JpaAiSessionStateStore(
                repository, new ObjectMapper(), leaseGuard, transactionTemplate);
        JpaAiSessionStateStore reader = new JpaAiSessionStateStore(
                repository, new ObjectMapper(), leaseGuard, transactionTemplate);
        Instant now = Instant.parse("2026-07-17T00:00:00Z");
        writer.put(1L, "session-1", AiSessionStateStore.Kind.DESTRUCTIVE_ACTION,
                JsonNodeFactory.instance.objectNode().put("token", "one-use"),
                now.plusSeconds(60));

        AiSessionStateStore.Snapshot snapshot = reader.get(
                1L, "session-1", AiSessionStateStore.Kind.DESTRUCTIVE_ACTION, now).orElseThrow();

        assertEquals("one-use", snapshot.payload().path("token").asText());
        assertTrue(reader.remove(1L, "session-1", AiSessionStateStore.Kind.DESTRUCTIVE_ACTION,
                snapshot.version()));
        assertFalse(writer.remove(1L, "session-1", AiSessionStateStore.Kind.DESTRUCTIVE_ACTION,
                snapshot.version()));
    }

    @Test
    void purgeExpiredRemovesRowsWithoutWaitingForSessionAccess() {
        JpaAiSessionStateStore store = new JpaAiSessionStateStore(
                repository, new ObjectMapper(), mock(ChatExecutionLeaseGuard.class), transactionTemplate);
        store.put(1L, "expired", AiSessionStateStore.Kind.SCENARIO_DRAFT,
                JsonNodeFactory.instance.objectNode(), Instant.now().minusSeconds(1));

        store.purgeExpired();

        assertTrue(repository.findAll().isEmpty());
    }

    @Test
    @Transactional(propagation = Propagation.NOT_SUPPORTED)
    void removeUserCanRunFromAfterCommitCleanup() {
        JpaAiSessionStateStore store = new JpaAiSessionStateStore(
                repository, new ObjectMapper(), mock(ChatExecutionLeaseGuard.class), transactionTemplate);
        AtomicReference<Throwable> cleanupFailure = new AtomicReference<>();

        transactionTemplate.executeWithoutResult(status -> {
            store.put(9L, "account-removal", AiSessionStateStore.Kind.TASK_CONTINUATION,
                    JsonNodeFactory.instance.objectNode().put("taskId", 41L),
                    Instant.now().plusSeconds(60));
            TransactionSynchronizationManager.registerSynchronization(new TransactionSynchronization() {
                @Override
                public void afterCommit() {
                    try {
                        store.removeUser(9L);
                    } catch (Throwable failure) {
                        cleanupFailure.set(failure);
                    }
                }
            });
        });

        assertNull(cleanupFailure.get());
        assertTrue(repository.findAll().isEmpty());
    }
}
