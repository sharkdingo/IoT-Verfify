package cn.edu.nju.Iot_Verify.component.ai.state;

import cn.edu.nju.Iot_Verify.repository.AiSessionStateRepository;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.JsonNodeFactory;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.jdbc.AutoConfigureTestDatabase;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;

import java.time.Instant;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

@DataJpaTest(properties = {
        "spring.jpa.database-platform=org.hibernate.dialect.H2Dialect",
        "spring.jpa.properties.hibernate.dialect=org.hibernate.dialect.H2Dialect",
        "spring.jpa.hibernate.ddl-auto=create-drop"
})
@AutoConfigureTestDatabase(replace = AutoConfigureTestDatabase.Replace.ANY)
class JpaAiSessionStateStoreTest {

    @Autowired
    private AiSessionStateRepository repository;

    @Test
    void stateSurvivesStoreInstancesAndIsConsumedWithCompareAndDelete() {
        JpaAiSessionStateStore writer = new JpaAiSessionStateStore(repository, new ObjectMapper());
        JpaAiSessionStateStore reader = new JpaAiSessionStateStore(repository, new ObjectMapper());
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
        JpaAiSessionStateStore store = new JpaAiSessionStateStore(repository, new ObjectMapper());
        store.put(1L, "expired", AiSessionStateStore.Kind.SCENARIO_DRAFT,
                JsonNodeFactory.instance.objectNode(), Instant.now().minusSeconds(1));

        store.purgeExpired();

        assertTrue(repository.findAll().isEmpty());
    }
}
