package cn.edu.nju.Iot_Verify.component.ai.state;

import com.fasterxml.jackson.databind.node.JsonNodeFactory;
import org.junit.jupiter.api.Test;

import java.time.Instant;

import static org.junit.jupiter.api.Assertions.assertEquals;

class InMemoryAiSessionStateStoreTest {

    @Test
    void fallbackNeverExceedsItsHardEntryLimit() {
        InMemoryAiSessionStateStore store = new InMemoryAiSessionStateStore();
        Instant expiresAt = Instant.now().plusSeconds(3600);

        for (int i = 0; i < InMemoryAiSessionStateStore.MAX_ENTRIES + 100; i++) {
            store.put(1L, "session-" + i, AiSessionStateStore.Kind.SCENARIO_DRAFT,
                    JsonNodeFactory.instance.objectNode().put("index", i), expiresAt);
        }

        assertEquals(InMemoryAiSessionStateStore.MAX_ENTRIES, store.size());
    }
}
