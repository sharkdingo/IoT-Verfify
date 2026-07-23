package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.repository.projection.SimulationTraceSummaryProjection;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.datatype.jsr310.JavaTimeModule;
import org.junit.jupiter.api.Test;

import java.time.LocalDateTime;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

class SimulationTraceMapperTest {

    private final SimulationTraceMapper mapper = new SimulationTraceMapper();
    private static final String VALID_STATE_JSON = "{\"stateIndex\":1,\"devices\":[],"
            + "\"triggeredRules\":[],\"compromisedAutomationLinks\":[]}";
    private static final String MODEL_SNAPSHOT_JSON = "{\"capturedAt\":\"2026-07-12T09:30:00\","
            + "\"deviceCount\":1,\"ruleCount\":1,\"specificationCount\":0,"
            + "\"environmentVariableCount\":0,\"deviceTemplateCount\":1,\"templatesFrozen\":true}";

    private static String stateJson(int stateIndex) {
        return "{\"stateIndex\":" + stateIndex + ",\"devices\":[],"
                + "\"triggeredRules\":[],\"compromisedAutomationLinks\":[]}";
    }

    private SimulationTracePo samplePo() {
        return SimulationTracePo.builder()
                .id(1L)
                .userId(42L)
                .requestedSteps(10)
                .steps(3)
                .statesJson("[" + stateJson(1) + "," + stateJson(2) + ","
                        + stateJson(3) + "," + stateJson(4) + "]")
                .stateCount(4)
                .logsJson("[\"log1\",\"log2\"]")
                .nusmvOutput("raw output")
                .requestJson("{\"devices\":[],\"rules\":[],\"steps\":10,\"isAttack\":true,\"attackBudget\":2,\"enablePrivacy\":true}")
                .templateSnapshotsJson("{\"light\":{\"Name\":\"Light\"}}")
                .modelSnapshotJson(MODEL_SNAPSHOT_JSON)
                .isAttack(true)
                .attackBudget(2)
                .enablePrivacy(true)
                .modeledDeviceAttackPointCount(1)
                .modeledFalsifiableReadingDeviceCount(1)
                .modeledAutomationLinkAttackPointCount(2)
                .createdAt(LocalDateTime.of(2026, 1, 1, 12, 0))
                .build();
    }

    @Test
    void toDto_null_returnsNull() {
        assertNull(mapper.toDto(null));
    }

    @Test
    void toDto_mapsAllFields() {
        SimulationTraceDto dto = mapper.toDto(samplePo());

        assertEquals(1L, dto.getId());
        assertEquals(42L, dto.getUserId());
        assertEquals(10, dto.getRequestedSteps());
        assertEquals(3, dto.getSteps());
        assertNotNull(dto.getStates());
        assertEquals(4, dto.getStates().size());
        assertEquals(List.of("log1", "log2"), dto.getLogs());
        assertEquals("raw output", dto.getNusmvOutput());
        assertTrue(dto.getRequestJson().contains("\"isAttack\":true"));
        assertEquals(Boolean.TRUE, dto.getAttack());
        assertEquals(2, dto.getAttackBudget());
        assertEquals(Boolean.TRUE, dto.getEnablePrivacy());
        assertEquals(1, dto.getModelSemantics().getModeledDeviceAttackPointCount());
        assertEquals(1, dto.getModelSemantics().getModeledFalsifiableReadingDeviceCount());
        assertEquals(2, dto.getModelSemantics().getModeledAutomationLinkAttackPointCount());
        assertEquals(1, dto.getModelSnapshot().getDeviceCount());
        assertTrue(dto.getModelSnapshot().isTemplatesFrozen());
        assertEquals("{\"light\":{\"Name\":\"Light\"}}", dto.getTemplateSnapshotsJson());
        assertEquals(LocalDateTime.of(2026, 1, 1, 12, 0), dto.getCreatedAt());
    }

    @Test
    void toDto_hidesInternalOwnershipAndRequestSnapshotFromJson() {
        ObjectMapper objectMapper = new ObjectMapper().registerModule(new JavaTimeModule());
        JsonNode json = objectMapper.valueToTree(mapper.toDto(samplePo()));

        assertFalse(json.has("userId"));
        assertFalse(json.has("requestJson"));
        assertFalse(json.has("templateSnapshotsJson"));
        assertTrue(json.path("modelSnapshot").path("templatesFrozen").asBoolean());
        assertTrue(json.path("isAttack").asBoolean());
        assertEquals(2, json.path("attackBudget").asInt());
    }
    @Test
    void toDto_nullStatesJson_failsClosed() {
        SimulationTracePo po = samplePo();
        po.setStatesJson(null);
        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));
        assertEquals("statesJson", error.getField());
    }

    @Test
    void toDto_emptyStatesJson_failsClosed() {
        SimulationTracePo po = samplePo();
        po.setStatesJson("[]");
        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));
        assertEquals("statesJson", error.getField());
    }

    @Test
    void toDto_structurallyInvalidStatesJson_failsClosed() {
        for (String statesJson : List.of("[null]", "[{}]")) {
            SimulationTracePo po = samplePo();
            po.setStatesJson(statesJson);
            PersistedDataIntegrityException error = assertThrows(
                    PersistedDataIntegrityException.class, () -> mapper.toDto(po));
            assertEquals("statesJson", error.getField());
        }
    }

    @Test
    void toDto_normalizesLegacyStatesWithoutRuleEventLists() {
        SimulationTracePo po = samplePo();
        po.setStatesJson("[{\"stateIndex\":1,\"devices\":[]}]");
        po.setSteps(0);
        po.setStateCount(1);

        SimulationTraceDto dto = mapper.toDto(po);

        assertEquals(1, dto.getStates().size());
        assertTrue(dto.getStates().get(0).getTriggeredRules().isEmpty());
        assertTrue(dto.getStates().get(0).getCompromisedAutomationLinks().isEmpty());
    }

    @Test
    void nonSequentialStateIndexesFailClosedInDetail() {
        for (String statesJson : List.of(
                "[" + stateJson(2) + "]",
                "[" + stateJson(1) + "," + stateJson(1) + "]",
                "[" + stateJson(1) + "," + stateJson(3) + "]")) {
            SimulationTracePo po = samplePo();
            po.setStatesJson(statesJson);

            assertEquals("statesJson", assertThrows(
                    PersistedDataIntegrityException.class, () -> mapper.toDto(po)).getField());
        }
    }

    @Test
    void incompleteTraceDeviceIdentityFailsClosedInDetail() {
        for (String deviceJson : List.of(
                "{\"deviceLabel\":\"Hall light\",\"templateName\":\"Light\",\"variables\":[]}",
                "{\"deviceId\":\"light_1\",\"templateName\":\"Light\",\"variables\":[]}",
                "{\"deviceId\":\"light_1\",\"deviceLabel\":\"Hall light\",\"variables\":[]}")) {
            SimulationTracePo po = samplePo();
            po.setStatesJson("[{\"stateIndex\":1,\"devices\":[" + deviceJson + "],"
                    + "\"triggeredRules\":[],\"compromisedAutomationLinks\":[]}]");

            assertEquals("statesJson", assertThrows(
                    PersistedDataIntegrityException.class, () -> mapper.toDto(po)).getField());
        }
    }

    @Test
    void missingPersistedRunContextFailsClosedInDetail() {
        SimulationTracePo missingAttack = samplePo();
        missingAttack.setIsAttack(null);
        assertEquals("isAttack", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(missingAttack)).getField());

        SimulationTracePo missingBudget = samplePo();
        missingBudget.setAttackBudget(null);
        assertEquals("attackBudget", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(missingBudget)).getField());

        SimulationTracePo missingPrivacy = samplePo();
        missingPrivacy.setEnablePrivacy(null);
        assertEquals("enablePrivacy", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(missingPrivacy)).getField());
    }

    @Test
    void summaryProjectionMapsWithoutDetailOnlySnapshots() {
        SimulationTraceSummaryProjection projection = mock(SimulationTraceSummaryProjection.class);
        when(projection.getId()).thenReturn(4L);
        when(projection.getRequestedSteps()).thenReturn(10);
        when(projection.getSteps()).thenReturn(2);
        when(projection.getStateCount()).thenReturn(3);
        when(projection.getLogsJson()).thenReturn("[]");
        when(projection.getGenerationIssuesJson()).thenReturn("[]");
        when(projection.getModelSnapshotJson()).thenReturn(MODEL_SNAPSHOT_JSON);
        when(projection.getIsAttack()).thenReturn(false);
        when(projection.getAttackBudget()).thenReturn(9);
        when(projection.getEnablePrivacy()).thenReturn(false);

        SimulationTraceSummaryDto summary = mapper.toSummaryProjectionDto(projection);

        assertEquals(4L, summary.getId());
        assertEquals(2, summary.getSteps());
        assertEquals(0, summary.getAttackBudget());
        assertTrue(summary.getDataAvailable());
    }

    @Test
    void summaryProjectionList_isolatesMissingPersistedRunContext() {
        SimulationTraceSummaryProjection projection = mock(SimulationTraceSummaryProjection.class);
        when(projection.getId()).thenReturn(5L);
        when(projection.getRequestedSteps()).thenReturn(1);
        when(projection.getSteps()).thenReturn(0);
        when(projection.getStateCount()).thenReturn(1);
        when(projection.getLogsJson()).thenReturn("[]");
        when(projection.getGenerationIssuesJson()).thenReturn("[]");
        when(projection.getModelSnapshotJson()).thenReturn(MODEL_SNAPSHOT_JSON);
        when(projection.getIsAttack()).thenReturn(false);
        when(projection.getAttackBudget()).thenReturn(0);
        when(projection.getEnablePrivacy()).thenReturn((Boolean) null);

        List<SimulationTraceSummaryDto> list = mapper.toSummaryProjectionDtoList(List.of(projection));

        assertEquals(1, list.size());
        assertFalse(list.get(0).getDataAvailable());
        assertEquals(5L, list.get(0).getId());
        assertEquals("PERSISTED_SEMANTIC_DATA_INVALID", list.get(0).getUnavailableReasonCode());
    }
}
