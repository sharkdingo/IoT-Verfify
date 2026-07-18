package cn.edu.nju.Iot_Verify.component.aitool.scenario;

import cn.edu.nju.Iot_Verify.component.ai.state.InMemoryAiSessionStateStore;
import cn.edu.nju.Iot_Verify.dto.board.BoardReplacementPreviewDto;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import java.time.Clock;
import java.time.Instant;
import java.time.ZoneOffset;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class AiScenarioDraftStoreTest {

    private final ObjectMapper objectMapper = new ObjectMapper();

    @Test
    void invalidReplacementDoesNotDeleteThePreviousValidDraft() throws Exception {
        AiScenarioDraftStore store = new AiScenarioDraftStore();
        store.saveDraft(1L, "session", "Existing", objectMapper.readTree(
                "{\"devices\":[{\"id\":\"device_1\"}],\"specs\":[]}"));

        AiScenarioDraftStore.DraftSaveResult result = store.saveDraft(
                1L, "session", "Invalid", objectMapper.readTree(
                "{\"devices\":[],\"specs\":[]}"));

        assertFalse(result.draftStored());
        assertTrue(result.previousDraftRetained());
        AiScenarioDraftStore.DraftSnapshot snapshot = store.latestDraft(1L, "session").orElseThrow();
        assertEquals("Existing", snapshot.scenarioName());
        assertTrue(snapshot.scene().path("devices").size() == 1);
    }

    @Test
    void anotherStoreInstanceCanReadThePersistedDraft() throws Exception {
        InMemoryAiSessionStateStore sharedState = new InMemoryAiSessionStateStore();
        Clock clock = Clock.fixed(Instant.parse("2026-07-17T00:00:00Z"), ZoneOffset.UTC);
        AiScenarioDraftStore writer = new AiScenarioDraftStore(sharedState, objectMapper, clock);
        AiScenarioDraftStore reader = new AiScenarioDraftStore(sharedState, objectMapper, clock);

        writer.saveDraft(1L, "session", "Shared", objectMapper.readTree(
                "{\"devices\":[{\"id\":\"device_1\"}],\"specs\":[]}"));

        assertEquals("Shared", reader.latestDraft(1L, "session").orElseThrow().scenarioName());
    }

    @Test
    void anotherStoreInstanceCanRecoverThePendingReplacementPreview() throws Exception {
        InMemoryAiSessionStateStore sharedState = new InMemoryAiSessionStateStore();
        Clock clock = Clock.fixed(Instant.parse("2026-07-17T00:00:00Z"), ZoneOffset.UTC);
        AiScenarioDraftStore writer = new AiScenarioDraftStore(sharedState, objectMapper, clock);
        AiScenarioDraftStore reader = new AiScenarioDraftStore(sharedState, objectMapper, clock);
        writer.saveDraft(1L, "session", "Shared", objectMapper.readTree("""
                {"devices":[{"id":"device_1"}],"specs":[]}
                """));
        writer.beginApplication(1L, "session", BoardReplacementPreviewDto.builder()
                .impactToken("board-v1")
                .deviceCount(3)
                .environmentVariableCount(2)
                .ruleCount(1)
                .specificationCount(4)
                .build());

        AiScenarioDraftStore.PendingApplication pending = reader
                .pendingApplication(1L, "session")
                .orElseThrow();

        assertEquals("board-v1", pending.preview().getImpactToken());
        assertEquals(3, pending.preview().getDeviceCount());
    }
}
