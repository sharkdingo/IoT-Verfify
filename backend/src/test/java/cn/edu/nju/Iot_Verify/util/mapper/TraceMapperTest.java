package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.model.ModelTokenSource;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.repository.projection.TraceSummaryProjection;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

class TraceMapperTest {

    private final TraceMapper mapper = new TraceMapper();
    private static final String VALID_STATE_JSON = "{\"stateIndex\":1,\"devices\":[],"
            + "\"triggeredRules\":[],\"compromisedAutomationLinks\":[]}";
    private static final String MODEL_SNAPSHOT_JSON = "{\"capturedAt\":\"2026-07-12T09:30:00\","
            + "\"deviceCount\":1,\"ruleCount\":1,\"specificationCount\":1,"
            + "\"environmentVariableCount\":0,\"deviceTemplateCount\":1,\"templatesFrozen\":true}";

    private static String stateJson(int stateIndex) {
        return "{\"stateIndex\":" + stateIndex + ",\"devices\":[],"
                + "\"triggeredRules\":[],\"compromisedAutomationLinks\":[]}";
    }

    private TracePo baseTrace(String requestJson) {
        TracePo po = new TracePo();
        po.setId(1L);
        po.setUserId(1L);
        po.setViolatedSpecId("s0");
        po.setViolatedSpecJson("{\"id\":\"s0\",\"templateId\":\"3\",\"templateLabel\":\"Never\","
                + "\"aConditions\":[],\"ifConditions\":[],\"thenConditions\":[],\"devices\":[]}");
        po.setStatesJson("[" + VALID_STATE_JSON + "]");
        po.setStateCount(1);
        po.setRequestJson(requestJson);
        po.setTemplateSnapshotsJson("{\"light\":{\"Name\":\"Light\"}}");
        po.setModelSnapshotJson(MODEL_SNAPSHOT_JSON);
        return po;
    }

    @Test
    void usesPersistedAttackContextInsteadOfRecountingRequestDevices() {
        TracePo po = baseTrace("{\"devices\":[{\"varName\":\"d1\",\"templateName\":\"t1\"}],"
                + "\"rules\":[{}],\"specs\":[],\"isAttack\":true,\"attackBudget\":1,\"enablePrivacy\":true}");
        po.setIsAttack(true);
        po.setAttackBudget(1);
        po.setEnablePrivacy(true);
        po.setModeledDeviceAttackPointCount(0);
        po.setModeledFalsifiableReadingDeviceCount(0);
        po.setModeledAutomationLinkAttackPointCount(1);

        TraceDto dto = mapper.toDto(po);

        assertEquals(Boolean.TRUE, dto.getAttack());
        assertEquals(1, dto.getAttackBudget());
        assertEquals(Boolean.TRUE, dto.getEnablePrivacy());
        assertEquals(0, dto.getModelSemantics().getModeledDeviceAttackPointCount());
        assertEquals(1, dto.getModelSemantics().getModeledAutomationLinkAttackPointCount());
        assertEquals(1, dto.getModelSemantics().getModeledAttackPointCount());
        assertEquals(1, dto.getModelSnapshot().getDeviceCount());
        assertTrue(dto.getModelSnapshot().isTemplatesFrozen());
        assertEquals(po.getTemplateSnapshotsJson(), dto.getTemplateSnapshotsJson());
    }

    @Test
    void normalizesPersistedDisabledAttackBudgetToZero() {
        TracePo po = baseTrace("{\"devices\":[{\"varName\":\"d1\",\"templateName\":\"t1\"}],"
                + "\"rules\":[],\"specs\":[]}");
        po.setIsAttack(false);
        po.setAttackBudget(7);
        po.setEnablePrivacy(false);
        po.setModeledDeviceAttackPointCount(0);
        po.setModeledFalsifiableReadingDeviceCount(0);
        po.setModeledAutomationLinkAttackPointCount(0);

        TraceDto dto = mapper.toDto(po);

        assertEquals(Boolean.FALSE, dto.getAttack());
        assertEquals(0, dto.getAttackBudget());
        assertEquals(Boolean.FALSE, dto.getEnablePrivacy());
    }

    @Test
    void traceWithoutPersistedModelContext_doesNotGuessFromRequestJson() {
        TracePo po = baseTrace("{\"devices\":[{\"varName\":\"d1\",\"templateName\":\"t1\"}],"
                + "\"rules\":[],\"specs\":[],\"isAttack\":true,\"attackBudget\":1}");

        TraceDto dto = mapper.toDto(po);

        assertNull(dto.getAttack());
        assertNull(dto.getAttackBudget());
        assertNull(dto.getEnablePrivacy());
    }

    @Test
    void unparseableInternalRequestSnapshot_doesNotAffectStructuredContext() {
        TracePo po = baseTrace("{ not valid json ");

        TraceDto dto = assertDoesNotThrow(() -> mapper.toDto(po));

        assertNull(dto.getAttack());
        assertNull(dto.getAttackBudget());
        assertNull(dto.getEnablePrivacy());
    }

    @Test
    void structurallyInvalidStatesFailClosedInDetail() {
        for (String statesJson : java.util.List.of("[null]", "[{}]")) {
            TracePo po = baseTrace(null);
            po.setStatesJson(statesJson);
            assertEquals("statesJson", assertThrows(
                    PersistedDataIntegrityException.class, () -> mapper.toDto(po)).getField());
        }
    }

    @Test
    void toDto_normalizesLegacyStatesWithoutRuleEventLists() {
        TracePo po = baseTrace(null);
        po.setStatesJson("[{\"stateIndex\":1,\"devices\":[]}]");

        TraceDto dto = mapper.toDto(po);

        assertEquals(1, dto.getStates().size());
        assertTrue(dto.getStates().get(0).getTriggeredRules().isEmpty());
        assertTrue(dto.getStates().get(0).getCompromisedAutomationLinks().isEmpty());
    }

    @Test
    void toDto_normalizesMissingLegacyTokenProvenanceToUnknown() {
        TracePo po = baseTrace(null);
        po.setStatesJson("[{\"stateIndex\":1,\"devices\":[{"
                + "\"deviceId\":\"light_1\",\"deviceLabel\":\"Hall light\","
                + "\"templateName\":\"Light\",\"variables\":[{"
                + "\"name\":\"workingState\",\"value\":\"off\"}]}],"
                + "\"triggeredRules\":[],\"compromisedAutomationLinks\":[],"
                + "\"envVariables\":[{\"name\":\"weather\",\"value\":\"sunny\"}]}]");

        TraceDto dto = mapper.toDto(po);

        var state = dto.getStates().get(0);
        assertEquals(ModelTokenSource.UNKNOWN,
                state.getDevices().get(0).getModelTokenSource());
        assertEquals(ModelTokenSource.UNKNOWN,
                state.getDevices().get(0).getVariables().get(0).getModelTokenSource());
        assertEquals(ModelTokenSource.UNKNOWN,
                state.getEnvVariables().get(0).getModelTokenSource());
    }

    @Test
    void nonSequentialStateIndexesFailClosedInDetail() {
        for (String statesJson : java.util.List.of(
                "[" + stateJson(2) + "]",
                "[" + stateJson(1) + "," + stateJson(1) + "]",
                "[" + stateJson(1) + "," + stateJson(3) + "]")) {
            TracePo po = baseTrace(null);
            po.setStatesJson(statesJson);

            assertEquals("statesJson", assertThrows(
                    PersistedDataIntegrityException.class, () -> mapper.toDto(po)).getField());
        }
    }

    @Test
    void incompleteTraceDeviceIdentityFailsClosedInDetail() {
        for (String deviceJson : java.util.List.of(
                "{\"deviceLabel\":\"Hall light\",\"templateName\":\"Light\",\"variables\":[]}",
                "{\"deviceId\":\"light_1\",\"templateName\":\"Light\",\"variables\":[]}",
                "{\"deviceId\":\"light_1\",\"deviceLabel\":\"Hall light\",\"variables\":[]}")) {
            TracePo po = baseTrace(null);
            po.setStatesJson("[{\"stateIndex\":1,\"devices\":[" + deviceJson + "],"
                    + "\"triggeredRules\":[],\"compromisedAutomationLinks\":[]}]");

            assertEquals("statesJson", assertThrows(
                    PersistedDataIntegrityException.class, () -> mapper.toDto(po)).getField());
        }
    }

    @Test
    void mapsPersistedSpecJsonToStructuredApiSnapshot() {
        TracePo po = baseTrace(null);
        po.setViolatedSpecJson("{\"id\":\"s0\",\"templateId\":\"3\",\"templateLabel\":\"Never\","
                + "\"aConditions\":[],\"ifConditions\":[],\"thenConditions\":[],\"devices\":[]}");

        TraceDto dto = mapper.toDto(po);

        assertNotNull(dto.getViolatedSpec());
        assertEquals("s0", dto.getViolatedSpec().getId());
        assertEquals("Never", dto.getViolatedSpec().getTemplateLabel());
    }

    @Test
    void preservesActualCheckedExpressionForHistoricalPlayback() {
        TracePo po = baseTrace(null);
        po.setCheckedExpression("CTLSPEC AG(!(camera_1.CameraMode=taking_photo))");

        TraceDto dto = mapper.toDto(po);
        TracePo roundTrip = mapper.toEntity(dto);

        assertEquals(po.getCheckedExpression(), dto.getCheckedExpression());
        assertEquals(po.getCheckedExpression(), roundTrip.getCheckedExpression());
    }

    @Test
    void toEntityPersistsExactRunAttackSurface() {
        TraceDto dto = new TraceDto();
        dto.setUserId(1L);
        dto.setViolatedSpecId("s0");
        cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto violatedSpec =
                new cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto();
        violatedSpec.setId("s0");
        violatedSpec.setTemplateId("3");
        dto.setViolatedSpec(violatedSpec);
        dto.setStates(java.util.List.of(new cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto()));
        dto.setAttack(true);
        dto.setAttackBudget(2);
        dto.setEnablePrivacy(false);
        dto.setModelSemantics(cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto.forRun(
                true, false, 1, 2, 1));
        dto.setTemplateSnapshotsJson("{\"light\":{\"Name\":\"Light\"}}");
        dto.setModelSnapshot(cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto.captured(
                java.time.LocalDateTime.of(2026, 7, 12, 9, 30), 1, 1, 1, 0, 1));

        TracePo po = mapper.toEntity(dto);

        assertEquals(Boolean.TRUE, po.getIsAttack());
        assertEquals(2, po.getAttackBudget());
        assertEquals(1, po.getModeledDeviceAttackPointCount());
        assertEquals(1, po.getModeledFalsifiableReadingDeviceCount());
        assertEquals(2, po.getModeledAutomationLinkAttackPointCount());
        assertEquals(dto.getTemplateSnapshotsJson(), po.getTemplateSnapshotsJson());
        assertEquals(1, po.getStateCount());
        assertTrue(po.getModelSnapshotJson().contains("\"templatesFrozen\":true"));
    }

    @Test
    void summaryProjectionCountsStatesWithoutLoadingDetailColumns() {
        TraceSummaryProjection projection = mock(TraceSummaryProjection.class);
        when(projection.getId()).thenReturn(8L);
        when(projection.getVerificationTaskId()).thenReturn(4L);
        when(projection.getViolatedSpecId()).thenReturn("s0");
        when(projection.getViolatedSpecJson()).thenReturn(
                "{\"id\":\"s0\",\"templateId\":\"3\",\"aConditions\":[],"
                        + "\"ifConditions\":[],\"thenConditions\":[],\"devices\":[]}");
        when(projection.getStateCount()).thenReturn(2);

        var summary = mapper.toSummaryDto(projection);

        assertEquals(2, summary.getStateCount());
        assertEquals(4L, summary.getVerificationTaskId());
    }
}
