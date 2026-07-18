package cn.edu.nju.Iot_Verify.component.aitool.scenario;

import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardReplacementPreviewDto;
import cn.edu.nju.Iot_Verify.exception.BoardReplacementStaleException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.doReturn;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ApplyScenarioToolTest {

    @Mock
    private ScenarioDraftBatchMapper batchMapper;
    @Mock
    private BoardStorageService boardStorageService;

    private final ObjectMapper objectMapper = new ObjectMapper();
    private AiScenarioDraftStore draftStore;
    private ApplyScenarioTool tool;

    @BeforeEach
    void setUp() throws Exception {
        draftStore = new AiScenarioDraftStore();
        tool = new ApplyScenarioTool(draftStore, batchMapper, boardStorageService, objectMapper);
        UserContextHolder.setUserId(1L);
        UserContextHolder.setChatSessionId("session-1");
        draftStore.saveDraft(1L, "session-1", "Night safety", scene());
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void execute_previewsThenAtomicallyAppliesOnlyAfterLaterExplicitConfirmation() throws Exception {
        BoardReplacementPreviewDto preview = preview("board-v1", 4, 2, 3, 5);
        when(boardStorageService.previewBoardReplacement(1L)).thenReturn(preview);

        JsonNode first = objectMapper.readTree(tool.execute("{\"confirmed\":false}"));

        assertTrue(first.path("requiresUserConfirmation").asBoolean());
        assertEquals("preview", first.path("operation").asText());
        assertEquals(4, first.path("currentDeviceCount").asInt());
        assertEquals(1, first.path("replacementDeviceCount").asInt());
        assertFalse(first.path("verificationReady").asBoolean());
        assertEquals("NO_SPECIFICATIONS", first.path("readinessIssues").get(0).path("code").asText());
        verify(boardStorageService, never()).saveBoardBatch(any(), any());

        BoardBatchDto request = new BoardBatchDto();
        BoardBatchDto saved = savedBatch();
        when(batchMapper.toBatch(any(), eq("board-v1"))).thenReturn(request);
        when(boardStorageService.saveBoardBatch(1L, request)).thenReturn(saved);
        UserContextHolder.setSceneReplacementConfirmed(true);

        JsonNode applied = objectMapper.readTree(tool.execute("{\"confirmed\":false}"));

        assertEquals("replaced", applied.path("operation").asText());
        assertEquals("NOT_VERIFIED", applied.path("verificationStatus").asText());
        assertFalse(applied.path("verificationReady").asBoolean());
        assertEquals(1, applied.path("deviceCount").asInt());
        assertFalse(draftStore.latestDraft(1L, "session-1").isPresent());
        verify(boardStorageService).saveBoardBatch(1L, request);
    }

    @Test
    void execute_whenBoardDrifts_returnsFreshPreviewAndRequiresAnotherConfirmation() throws Exception {
        BoardReplacementPreviewDto firstPreview = preview("board-v1", 1, 0, 0, 0);
        BoardReplacementPreviewDto freshPreview = preview("board-v2", 2, 0, 1, 0);
        when(boardStorageService.previewBoardReplacement(1L)).thenReturn(firstPreview);
        tool.execute("{\"confirmed\":false}");

        BoardBatchDto firstRequest = new BoardBatchDto();
        firstRequest.setImpactToken("board-v1");
        when(batchMapper.toBatch(any(), eq("board-v1"))).thenReturn(firstRequest);
        when(boardStorageService.saveBoardBatch(1L, firstRequest))
                .thenThrow(new BoardReplacementStaleException(freshPreview));
        UserContextHolder.setSceneReplacementConfirmed(true);

        JsonNode stale = objectMapper.readTree(tool.execute("{\"confirmed\":true}"));

        assertEquals("BOARD_REPLACEMENT_STALE", stale.path("errorCode").asText());
        assertTrue(stale.path("requiresUserConfirmation").asBoolean());
        assertEquals(2, stale.path("currentDeviceCount").asInt());

        BoardBatchDto secondRequest = new BoardBatchDto();
        secondRequest.setImpactToken("board-v2");
        when(batchMapper.toBatch(any(), eq("board-v2"))).thenReturn(secondRequest);
        doReturn(savedBatch()).when(boardStorageService).saveBoardBatch(1L, secondRequest);

        JsonNode applied = objectMapper.readTree(tool.execute("{\"confirmed\":true}"));

        assertEquals("replaced", applied.path("operation").asText());
        verify(boardStorageService).saveBoardBatch(1L, secondRequest);
    }

    @Test
    void execute_doesNotTreatDeletionConfirmationAsSceneReplacementAuthorization() throws Exception {
        BoardReplacementPreviewDto preview = preview("board-v1", 1, 0, 0, 0);
        when(boardStorageService.previewBoardReplacement(1L)).thenReturn(preview);
        tool.execute("{\"confirmed\":false}");
        UserContextHolder.setDestructiveActionConfirmed(true);

        JsonNode result = objectMapper.readTree(tool.execute("{\"confirmed\":true}"));

        assertEquals("preview", result.path("operation").asText());
        assertTrue(result.path("requiresUserConfirmation").asBoolean());
        verify(boardStorageService, never()).saveBoardBatch(any(), any());
    }

    private JsonNode scene() throws Exception {
        return objectMapper.readTree("""
                {
                  "templates":[],
                  "devices":[{"id":"device_1"}],
                  "environmentVariables":[],
                  "rules":[],
                  "specs":[]
                }
                """);
    }

    private BoardReplacementPreviewDto preview(String token,
                                                int devices,
                                                int variables,
                                                int rules,
                                                int specs) {
        return BoardReplacementPreviewDto.builder()
                .impactToken(token)
                .deviceCount(devices)
                .environmentVariableCount(variables)
                .ruleCount(rules)
                .specificationCount(specs)
                .build();
    }

    private BoardBatchDto savedBatch() {
        BoardBatchDto saved = new BoardBatchDto();
        saved.setNodes(List.of(new cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto()));
        saved.setEnvironmentVariables(List.of());
        saved.setRules(List.of());
        saved.setSpecs(List.of());
        saved.setCreatedTemplates(List.of());
        return saved;
    }
}
