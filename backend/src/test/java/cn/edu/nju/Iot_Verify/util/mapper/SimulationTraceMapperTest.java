package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.repository.projection.SimulationTraceSummaryProjection;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
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
            + "\"deviceCount\":1,\"ruleCount\":2,\"specificationCount\":0,"
            + "\"environmentVariableCount\":0,\"deviceTemplateCount\":1,\"templatesFrozen\":true}";
    private static final String MODEL_SEMANTICS_JSON = JsonUtils.toJson(
            ModelSemanticsDto.forRun(AttackScenarioDto.anyUpToBudget(2), true, 1, 2, 1));
    private static final String VALID_REQUEST_JSON = "{\"devices\":[],\"rules\":["
            + "{\"id\":42,\"ruleString\":\"Rule A\"},"
            + "{\"id\":43,\"ruleString\":\"Rule B\"}],\"steps\":10,"
            + "\"attackScenario\":{\"mode\":\"ANY_UP_TO_BUDGET\",\"budget\":2},"
            + "\"enablePrivacy\":true}";

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
                .requestJson(VALID_REQUEST_JSON)
                .templateSnapshotsJson("{\"light\":{\"Name\":\"Light\"}}")
                .modelSnapshotJson(MODEL_SNAPSHOT_JSON)
                .modelSemanticsJson(MODEL_SEMANTICS_JSON)
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
        assertTrue(dto.getRequestJson().contains("\"mode\":\"ANY_UP_TO_BUDGET\""));
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
    void toDto_rejectsStatesWithoutRequiredRuleEventLists() {
        SimulationTracePo po = samplePo();
        po.setStatesJson("[{\"stateIndex\":1,\"devices\":[]}]");
        po.setSteps(0);
        po.setStateCount(1);

        assertEquals("statesJson", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po)).getField());
    }

    @Test
    void toDto_bindsRuleEvidenceToTheFrozenRequestSnapshot() {
        SimulationTracePo valid = samplePo();
        valid.setStatesJson("[{\"stateIndex\":1,\"devices\":[],"
                + "\"triggeredRules\":[{\"ruleIndex\":1,\"ruleId\":\"43\","
                + "\"ruleLabel\":\"Rule B\"}],\"compromisedAutomationLinks\":[]}]");
        valid.setSteps(0);
        valid.setStateCount(1);
        assertDoesNotThrow(() -> mapper.toDto(valid));

        for (String evidence : List.of(
                "{\"ruleIndex\":2}",
                "{\"ruleIndex\":1,\"ruleId\":\"99\",\"ruleLabel\":\"Rule B\"}",
                "{\"ruleIndex\":1,\"ruleId\":\"43\",\"ruleLabel\":\"Forged\"}")) {
            SimulationTracePo corrupt = samplePo();
            corrupt.setStatesJson("[{\"stateIndex\":1,\"devices\":[],"
                    + "\"triggeredRules\":[],\"compromisedAutomationLinks\":["
                    + evidence + "]}]");
            corrupt.setSteps(0);
            corrupt.setStateCount(1);

            assertEquals("statesJson", assertThrows(
                    PersistedDataIntegrityException.class, () -> mapper.toDto(corrupt)).getField());
        }
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

        SimulationTracePo missingSemantics = samplePo();
        missingSemantics.setModelSemanticsJson(null);
        assertEquals("modelSemanticsJson", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(missingSemantics)).getField());
    }

    @Test
    void summaryProjectionRejectsInconsistentAttackContext() {
        SimulationTraceSummaryProjection projection = validProjection(4L);
        when(projection.getIsAttack()).thenReturn(false);
        when(projection.getAttackBudget()).thenReturn(9);
        when(projection.getEnablePrivacy()).thenReturn(false);

        assertEquals("attackBudget", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toSummaryProjectionDto(projection)).getField());
    }

    @Test
    void summaryProjectionList_isolatesMissingPersistedRunContext() {
        SimulationTraceSummaryProjection projection = validProjection(5L);
        when(projection.getRequestedSteps()).thenReturn(1);
        when(projection.getSteps()).thenReturn(0);
        when(projection.getStateCount()).thenReturn(1);
        when(projection.getStatesJson()).thenReturn("[" + stateJson(1) + "]");
        when(projection.getEnablePrivacy()).thenReturn((Boolean) null);

        List<SimulationTraceSummaryDto> list = mapper.toSummaryProjectionDtoList(List.of(projection));

        assertEquals(1, list.size());
        assertFalse(list.get(0).getDataAvailable());
        assertEquals(5L, list.get(0).getId());
        assertEquals("PERSISTED_SEMANTIC_DATA_INVALID", list.get(0).getUnavailableReasonCode());
    }

    @Test
    void summaryProjectionListDoesNotMisreportProgrammingErrorsAsCorruptData() {
        SimulationTraceSummaryProjection projection = mock(SimulationTraceSummaryProjection.class);
        when(projection.getId()).thenThrow(new IllegalStateException("unexpected mapper bug"));

        assertThrows(IllegalStateException.class,
                () -> mapper.toSummaryProjectionDtoList(List.of(projection)));
    }

    @Test
    void emptyOrContradictoryStructuredContextFailsClosed() {
        SimulationTracePo emptySemantics = samplePo();
        emptySemantics.setModelSemanticsJson("{}");
        assertEquals("modelSemanticsJson", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toDto(emptySemantics)).getField());

        SimulationTracePo emptySnapshot = samplePo();
        emptySnapshot.setModelSnapshotJson("{}");
        assertEquals("modelSnapshotJson", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toDto(emptySnapshot)).getField());

        SimulationTracePo contradictoryCounts = samplePo();
        contradictoryCounts.setModeledDeviceAttackPointCount(0);
        assertEquals("modelSemanticsJson", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toDto(contradictoryCounts)).getField());
    }

    @Test
    void summaryProjectionValidatesSemanticsThatAreNotReturnedInTheSummary() {
        SimulationTraceSummaryProjection projection = validProjection(6L);
        when(projection.getModelSemanticsJson()).thenReturn("{}");

        assertEquals("modelSemanticsJson", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toSummaryProjectionDto(projection)).getField());
    }

    @Test
    void summaryProjectionValidatesStatesAndMapsSummary() {
        SimulationTraceSummaryDto summary = mapper.toSummaryProjectionDto(validProjection(7L));

        assertEquals(7L, summary.getId());
        assertEquals(2, summary.getSteps());
        assertTrue(summary.getDataAvailable());
    }

    @Test
    void summaryProjectionRejectsMalformedStatesJson() {
        SimulationTraceSummaryProjection projection = validProjection(8L);
        when(projection.getStatesJson()).thenReturn("{ not valid json");

        assertEquals("statesJson", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toSummaryProjectionDto(projection)).getField());
    }

    @Test
    void summaryProjectionRejectsOutOfRangeFrozenRuleEvidence() {
        SimulationTraceSummaryProjection projection = validProjection(11L);
        when(projection.getStatesJson()).thenReturn(
                "[{\"stateIndex\":1,\"devices\":[],\"triggeredRules\":[],"
                        + "\"compromisedAutomationLinks\":[]},"
                        + "{\"stateIndex\":2,\"devices\":[],"
                        + "\"triggeredRules\":[{\"ruleIndex\":2}],"
                        + "\"compromisedAutomationLinks\":[]},"
                        + "{\"stateIndex\":3,\"devices\":[],\"triggeredRules\":[],"
                        + "\"compromisedAutomationLinks\":[]}]");

        assertEquals("statesJson", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toSummaryProjectionDto(projection)).getField());
    }

    @Test
    void summaryProjectionRejectsEmptyStructurallyInvalidOrNonSequentialStates() {
        for (String statesJson : List.of(
                "[]", "[{}]", "[" + stateJson(2) + "]")) {
            SimulationTraceSummaryProjection projection = validProjection(9L);
            when(projection.getStatesJson()).thenReturn(statesJson);

            assertEquals("statesJson", assertThrows(
                    PersistedDataIntegrityException.class,
                    () -> mapper.toSummaryProjectionDto(projection)).getField());
        }
    }

    @Test
    void summaryProjectionRejectsStateCountMismatch() {
        SimulationTraceSummaryProjection projection = validProjection(10L);
        when(projection.getStatesJson()).thenReturn(
                "[" + stateJson(1) + "," + stateJson(2) + "]");

        assertEquals("stateCount", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toSummaryProjectionDto(projection)).getField());
    }

    private SimulationTraceSummaryProjection validProjection(Long id) {
        SimulationTraceSummaryProjection projection = mock(SimulationTraceSummaryProjection.class);
        when(projection.getId()).thenReturn(id);
        when(projection.getRequestedSteps()).thenReturn(10);
        when(projection.getSteps()).thenReturn(2);
        when(projection.getStateCount()).thenReturn(3);
        when(projection.getStatesJson()).thenReturn(
                "[" + stateJson(1) + "," + stateJson(2) + "," + stateJson(3) + "]");
        when(projection.getLogsJson()).thenReturn("[]");
        when(projection.getGenerationIssuesJson()).thenReturn("[]");
        when(projection.getRequestJson()).thenReturn(VALID_REQUEST_JSON);
        when(projection.getModelSnapshotJson()).thenReturn(MODEL_SNAPSHOT_JSON);
        when(projection.getModelSemanticsJson()).thenReturn(MODEL_SEMANTICS_JSON);
        when(projection.getIsAttack()).thenReturn(true);
        when(projection.getAttackBudget()).thenReturn(2);
        when(projection.getEnablePrivacy()).thenReturn(true);
        when(projection.getModeledDeviceAttackPointCount()).thenReturn(1);
        when(projection.getModeledFalsifiableReadingDeviceCount()).thenReturn(1);
        when(projection.getModeledAutomationLinkAttackPointCount()).thenReturn(2);
        return projection;
    }
}
