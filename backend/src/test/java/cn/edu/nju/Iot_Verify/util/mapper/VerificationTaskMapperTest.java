package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueReasonCode;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.TaskProgressStage;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationOutcome;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import cn.edu.nju.Iot_Verify.repository.projection.VerificationRunSummaryProjection;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import org.junit.jupiter.api.Test;

import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

class VerificationTaskMapperTest {

    private final VerificationTaskMapper mapper = new VerificationTaskMapper();
    private static final LocalDateTime CREATED_AT = LocalDateTime.of(2026, 7, 12, 9, 30);
    private static final String MODEL_SNAPSHOT_JSON = "{\"capturedAt\":\"2026-07-12T09:30:00\","
            + "\"deviceCount\":3,\"ruleCount\":2,\"specificationCount\":1,"
            + "\"environmentVariableCount\":1,\"deviceTemplateCount\":2,\"templatesFrozen\":true}";
    private static final String ATTACK_MODEL_SEMANTICS_JSON = JsonUtils.toJson(ModelSemanticsDto.forRun(
            AttackScenarioDto.anyUpToBudget(2), true, 3, 2, 1));
    private static final String NO_ATTACK_MODEL_SEMANTICS_JSON = JsonUtils.toJson(ModelSemanticsDto.forRun(
            AttackScenarioDto.none(), false, 3, 2, 1));

    @Test
    void mapsStructuredSpecResultsAndLogs() {
        VerificationTaskPo po = VerificationTaskPo.builder()
                .id(7L)
                .userId(1L)
                .status(VerificationTaskPo.TaskStatus.COMPLETED)
                .createdAt(CREATED_AT)
                .startedAt(CREATED_AT)
                .completedAt(CREATED_AT.plusSeconds(1))
                .processingTimeMs(1_000L)
                .progress(100)
                .progressStage(TaskProgressStage.PARSING_RESULTS)
                .isAttack(true)
                .attackBudget(2)
                .modeledDeviceAttackPointCount(3)
                .modeledFalsifiableReadingDeviceCount(1)
                .modeledAutomationLinkAttackPointCount(2)
                .enablePrivacy(true)
                .modelSemanticsJson(ATTACK_MODEL_SEMANTICS_JSON)
                .modelSnapshotJson(MODEL_SNAPSHOT_JSON)
                .outcome(VerificationOutcome.VIOLATED)
                .violatedSpecCount(1)
                .disabledRuleCount(1)
                .skippedSpecCount(0)
                .specResultsJson("[{\"specId\":\"s1\",\"outcome\":\"SATISFIED\",\"expression\":\"CTLSPEC AG(light.on)\"}]")
                .generationIssuesJson("[{\"issueType\":\"RULE_DISABLED\",\"itemLabel\":\"Hall automation\","
                        + "\"reasonCode\":\"RULE_UNRESOLVABLE_TRIGGER_CONDITION\",\"reason\":\"Unsupported action\"}]")
                .checkLogsJson("[\"generated\",\"checked\"]")
                .nusmvOutput("raw output")
                .build();

        VerificationTaskDto dto = mapper.toDto(po);

        assertEquals(1, dto.getSpecResults().size());
        assertEquals(TaskProgressStage.PARSING_RESULTS, dto.getProgressStage());
        assertEquals("s1", dto.getSpecResults().get(0).getSpecId());
        assertEquals(VerificationOutcome.SATISFIED, dto.getSpecResults().get(0).getOutcome());
        assertEquals("CTLSPEC AG(light.on)", dto.getSpecResults().get(0).getExpression());
        assertEquals(java.util.List.of("generated", "checked"), dto.getCheckLogs());
        assertEquals("raw output", dto.getNusmvOutput());
        assertEquals(VerificationOutcome.VIOLATED, dto.getOutcome());
        assertEquals(true, dto.getIsAttack());
        assertEquals(2, dto.getAttackBudget());
        assertEquals(true, dto.getEnablePrivacy());
        assertEquals(3, dto.getModelSemantics().getModeledDeviceAttackPointCount());
        assertEquals(1, dto.getModelSemantics().getModeledFalsifiableReadingDeviceCount());
        assertEquals(2, dto.getModelSemantics().getModeledAutomationLinkAttackPointCount());
        assertEquals(5, dto.getModelSemantics().getModeledAttackPointCount());
        assertEquals(3, dto.getModelSnapshot().getDeviceCount());
        assertEquals(1, dto.getModelSnapshot().getSpecificationCount());
        assertEquals(true, dto.getModelSnapshot().isTemplatesFrozen());
        assertEquals(false, dto.getModelComplete());
        VerificationTaskSummaryDto summary = mapper.toSummaryDto(po);
        assertEquals(TaskProgressStage.PARSING_RESULTS, summary.getProgressStage());
        assertEquals("Hall automation", summary.getGenerationIssues().get(0).getItemLabel());
        assertEquals(ModelGenerationIssueReasonCode.RULE_UNRESOLVABLE_TRIGGER_CONDITION,
                summary.getGenerationIssues().get(0).getReasonCode());
        assertEquals(true, summary.getIsAttack());
        assertEquals(2, summary.getAttackBudget());
        assertEquals(true, summary.getEnablePrivacy());
        assertEquals(5, summary.getModelSemantics().getModeledAttackPointCount());
        assertEquals(dto.getModelSnapshot(), summary.getModelSnapshot());
        var run = mapper.toRunDto(po, 1);
        assertEquals(1, run.getCounterexampleCount());
        assertEquals("raw output", run.getNusmvOutput());
        assertEquals(java.util.List.of("generated", "checked"), run.getCheckLogs());
    }

    @Test
    void mapsCompletedInconclusiveTaskWithoutCallingItViolation() {
        VerificationTaskPo po = VerificationTaskPo.builder()
                .id(8L)
                .userId(1L)
                .status(VerificationTaskPo.TaskStatus.COMPLETED)
                .createdAt(CREATED_AT)
                .startedAt(CREATED_AT)
                .completedAt(CREATED_AT.plusSeconds(1))
                .processingTimeMs(1_000L)
                .progress(100)
                .isAttack(false)
                .attackBudget(0)
                .modeledDeviceAttackPointCount(3)
                .modeledFalsifiableReadingDeviceCount(1)
                .modeledAutomationLinkAttackPointCount(2)
                .enablePrivacy(false)
                .modelSemanticsJson(NO_ATTACK_MODEL_SEMANTICS_JSON)
                .modelSnapshotJson(MODEL_SNAPSHOT_JSON)
                .outcome(VerificationOutcome.INCONCLUSIVE)
                .violatedSpecCount(1)
                .disabledRuleCount(0)
                .skippedSpecCount(0)
                .checkLogsJson("[\"[verification-inconclusive] result parsing was incomplete\"]")
                .build();

        VerificationTaskDto dto = mapper.toDto(po);

        assertEquals(VerificationOutcome.INCONCLUSIVE, dto.getOutcome());
        assertEquals(false, dto.getModelComplete());
    }

    @Test
    void runMappersKeepTheReplayableCountSuppliedByTheService() {
        VerificationTaskPo po = VerificationTaskPo.builder()
                .id(10L)
                .userId(1L)
                .status(VerificationTaskPo.TaskStatus.COMPLETED)
                .createdAt(CREATED_AT)
                .startedAt(CREATED_AT)
                .completedAt(CREATED_AT.plusSeconds(1))
                .processingTimeMs(1_000L)
                .progress(100)
                .isAttack(false)
                .attackBudget(0)
                .modeledDeviceAttackPointCount(3)
                .modeledFalsifiableReadingDeviceCount(1)
                .modeledAutomationLinkAttackPointCount(2)
                .enablePrivacy(false)
                .modelSemanticsJson(NO_ATTACK_MODEL_SEMANTICS_JSON)
                .modelSnapshotJson(MODEL_SNAPSHOT_JSON)
                .outcome(VerificationOutcome.VIOLATED)
                .violatedSpecCount(1)
                .disabledRuleCount(0)
                .skippedSpecCount(0)
                .checkLogsJson("[]")
                .build();

        assertEquals(0, mapper.toRunDto(po, 0).getCounterexampleCount());

        VerificationRunSummaryProjection projection = mock(VerificationRunSummaryProjection.class);
        when(projection.getId()).thenReturn(10L);
        when(projection.getStatus()).thenReturn(VerificationTaskPo.TaskStatus.COMPLETED);
        when(projection.getCreatedAt()).thenReturn(CREATED_AT);
        when(projection.getStartedAt()).thenReturn(CREATED_AT);
        when(projection.getCompletedAt()).thenReturn(CREATED_AT.plusSeconds(1));
        when(projection.getProcessingTimeMs()).thenReturn(1_000L);
        when(projection.getIsAttack()).thenReturn(false);
        when(projection.getAttackBudget()).thenReturn(0);
        when(projection.getEnablePrivacy()).thenReturn(false);
        when(projection.getModeledDeviceAttackPointCount()).thenReturn(3);
        when(projection.getModeledFalsifiableReadingDeviceCount()).thenReturn(1);
        when(projection.getModeledAutomationLinkAttackPointCount()).thenReturn(2);
        when(projection.getOutcome()).thenReturn(VerificationOutcome.VIOLATED);
        when(projection.getViolatedSpecCount()).thenReturn(1);
        when(projection.getDisabledRuleCount()).thenReturn(0);
        when(projection.getSkippedSpecCount()).thenReturn(0);
        when(projection.getModelSemanticsJson()).thenReturn(NO_ATTACK_MODEL_SEMANTICS_JSON);
        when(projection.getModelSnapshotJson()).thenReturn(MODEL_SNAPSHOT_JSON);
        when(projection.getGenerationIssuesJson()).thenReturn("[]");

        var summary = mapper.toRunSummaryDto(projection, 0);
        assertEquals(0, summary.getCounterexampleCount());
        assertEquals(VerificationOutcome.VIOLATED, summary.getOutcome());
    }

    @Test
    void missingModelSnapshotFailsClosed() {
        VerificationTaskPo po = VerificationTaskPo.builder()
                .id(9L)
                .userId(1L)
                .status(VerificationTaskPo.TaskStatus.COMPLETED)
                .createdAt(CREATED_AT)
                .startedAt(CREATED_AT)
                .completedAt(CREATED_AT.plusSeconds(1))
                .processingTimeMs(1_000L)
                .progress(100)
                .isAttack(false)
                .attackBudget(0)
                .modeledDeviceAttackPointCount(3)
                .modeledFalsifiableReadingDeviceCount(1)
                .modeledAutomationLinkAttackPointCount(2)
                .enablePrivacy(false)
                .modelSemanticsJson(NO_ATTACK_MODEL_SEMANTICS_JSON)
                .outcome(VerificationOutcome.INCONCLUSIVE)
                .violatedSpecCount(0)
                .disabledRuleCount(0)
                .skippedSpecCount(0)
                .build();

        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));

        assertEquals("modelSnapshotJson", error.getField());
    }

    @Test
    void missingModelSemanticsFailsClosed() {
        VerificationTaskPo po = VerificationTaskPo.builder()
                .id(11L)
                .userId(1L)
                .status(VerificationTaskPo.TaskStatus.PENDING)
                .createdAt(CREATED_AT)
                .progress(0)
                .isAttack(false)
                .attackBudget(0)
                .modeledDeviceAttackPointCount(3)
                .modeledFalsifiableReadingDeviceCount(1)
                .modeledAutomationLinkAttackPointCount(2)
                .enablePrivacy(false)
                .modelSnapshotJson(MODEL_SNAPSHOT_JSON)
                .build();

        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));

        assertEquals("modelSemanticsJson", error.getField());
    }

    @Test
    void emptyStructuredModelContextFailsClosed() {
        VerificationTaskPo invalidSemantics = validCompletedTask(12L);
        invalidSemantics.setModelSemanticsJson("{}");
        assertEquals("modelSemanticsJson", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toDto(invalidSemantics)).getField());

        VerificationTaskPo invalidSnapshot = validCompletedTask(13L);
        invalidSnapshot.setModelSnapshotJson("{}");
        assertEquals("modelSnapshotJson", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(invalidSnapshot)).getField());
    }

    @Test
    void contradictoryModelSemanticsFailsClosed() {
        VerificationTaskPo po = validCompletedTask(14L);
        po.setEnablePrivacy(true);

        assertEquals("modelSemanticsJson", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po)).getField());

        VerificationTaskPo missingAttackEffects = validCompletedTask(19L);
        missingAttackEffects.setIsAttack(true);
        missingAttackEffects.setAttackBudget(2);
        missingAttackEffects.setEnablePrivacy(true);
        ModelSemanticsDto semantics = ModelSemanticsDto.forRun(
                AttackScenarioDto.anyUpToBudget(2), true, 3, 2, 1);
        semantics.setAttackEffects(java.util.List.of());
        missingAttackEffects.setModelSemanticsJson(JsonUtils.toJson(semantics));
        assertEquals("modelSemanticsJson", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toDto(missingAttackEffects)).getField());
    }

    @Test
    void nullRunContextScalarsFailClosedInsteadOfDefaulting() {
        VerificationTaskPo missingAttack = validCompletedTask(15L);
        missingAttack.setIsAttack(null);
        assertEquals("isAttack", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(missingAttack)).getField());

        VerificationTaskPo missingBudget = validCompletedTask(16L);
        missingBudget.setAttackBudget(null);
        assertEquals("attackBudget", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(missingBudget)).getField());

        VerificationTaskPo missingPrivacy = validCompletedTask(17L);
        missingPrivacy.setEnablePrivacy(null);
        assertEquals("enablePrivacy", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(missingPrivacy)).getField());
    }

    @Test
    void terminalTaskWithoutOutcomeFailsClosed() {
        VerificationTaskPo po = validCompletedTask(18L);
        po.setOutcome(null);

        assertEquals("outcome", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po)).getField());
    }

    @Test
    void contradictoryTaskLifecycleFailsClosed() {
        VerificationTaskPo missingStart = validCompletedTask(20L);
        missingStart.setStartedAt(null);
        missingStart.setProcessingTimeMs(null);
        assertEquals("startedAt", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toDto(missingStart)).getField());

        VerificationTaskPo completionBeforeStart = validCompletedTask(21L);
        completionBeforeStart.setCompletedAt(CREATED_AT.minusSeconds(1));
        assertEquals("completedAt", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toSummaryDto(completionBeforeStart)).getField());

        VerificationTaskPo negativeProcessingTime = validCompletedTask(22L);
        negativeProcessingTime.setProcessingTimeMs(-1L);
        assertEquals("processingTimeMs", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toDto(negativeProcessingTime)).getField());

        VerificationTaskPo incompleteProgress = validCompletedTask(23L);
        incompleteProgress.setProgress(99);
        assertEquals("progress", assertThrows(
                PersistedDataIntegrityException.class,
                () -> mapper.toDto(incompleteProgress)).getField());
    }

    private VerificationTaskPo validCompletedTask(Long id) {
        return VerificationTaskPo.builder()
                .id(id)
                .userId(1L)
                .status(VerificationTaskPo.TaskStatus.COMPLETED)
                .createdAt(CREATED_AT)
                .startedAt(CREATED_AT)
                .completedAt(CREATED_AT.plusSeconds(1))
                .processingTimeMs(1_000L)
                .progress(100)
                .isAttack(false)
                .attackBudget(0)
                .modeledDeviceAttackPointCount(3)
                .modeledFalsifiableReadingDeviceCount(1)
                .modeledAutomationLinkAttackPointCount(2)
                .enablePrivacy(false)
                .modelSemanticsJson(NO_ATTACK_MODEL_SEMANTICS_JSON)
                .modelSnapshotJson(MODEL_SNAPSHOT_JSON)
                .outcome(VerificationOutcome.INCONCLUSIVE)
                .violatedSpecCount(0)
                .disabledRuleCount(0)
                .skippedSpecCount(0)
                .checkLogsJson("[]")
                .build();
    }
}
