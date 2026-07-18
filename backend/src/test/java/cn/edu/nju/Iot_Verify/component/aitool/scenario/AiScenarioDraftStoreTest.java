package cn.edu.nju.Iot_Verify.component.aitool.scenario;

import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class AiScenarioDraftStoreTest {

    private final ObjectMapper objectMapper = new ObjectMapper();

    @Test
    void invalidReplacementDoesNotDeleteThePreviousValidDraft() throws Exception {
        AiScenarioDraftStore store = new AiScenarioDraftStore();
        store.saveDraft(1L, "session", "Existing", objectMapper.readTree(
                "{\"devices\":[{\"id\":\"device_1\"}],\"specs\":[]}"));

        store.saveDraft(1L, "session", "Invalid", objectMapper.readTree(
                "{\"devices\":[],\"specs\":[]}"));

        AiScenarioDraftStore.DraftSnapshot snapshot = store.latestDraft(1L, "session").orElseThrow();
        assertEquals("Existing", snapshot.scenarioName());
        assertTrue(snapshot.scene().path("devices").size() == 1);
    }
}
