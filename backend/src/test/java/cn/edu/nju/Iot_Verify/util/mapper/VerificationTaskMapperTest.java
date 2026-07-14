package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueReasonCode;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationOutcome;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import org.junit.jupiter.api.Test;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;

import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class VerificationTaskMapperTest {

    private final VerificationTaskMapper mapper = new VerificationTaskMapper();
    private static final String MODEL_SNAPSHOT_JSON = "{\"capturedAt\":\"2026-07-12T09:30:00\","
            + "\"deviceCount\":2,\"ruleCount\":1,\"specificationCount\":1,"
            + "\"environmentVariableCount\":1,\"deviceTemplateCount\":2,\"templatesFrozen\":true}";

    @Test
    void mapsStructuredSpecResultsAndLogs() {
        VerificationTaskPo po = VerificationTaskPo.builder()
                .id(7L)
                .userId(1L)
                .status(VerificationTaskPo.TaskStatus.COMPLETED)
                .createdAt(LocalDateTime.now())
                .isAttack(true)
                .attackBudget(2)
                .modeledDeviceAttackPointCount(3)
                .modeledFalsifiableReadingDeviceCount(1)
                .modeledAutomationLinkAttackPointCount(2)
                .enablePrivacy(true)
                .modelSnapshotJson(MODEL_SNAPSHOT_JSON)
                .outcome(VerificationOutcome.VIOLATED)
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
        assertEquals(2, dto.getModelSnapshot().getDeviceCount());
        assertEquals(1, dto.getModelSnapshot().getSpecificationCount());
        assertEquals(true, dto.getModelSnapshot().isTemplatesFrozen());
        assertEquals(false, dto.getModelComplete());
        VerificationTaskSummaryDto summary = mapper.toSummaryDto(po);
        assertEquals("Hall automation", summary.getGenerationIssues().get(0).getItemLabel());
        assertEquals(ModelGenerationIssueReasonCode.RULE_UNRESOLVABLE_TRIGGER_CONDITION,
                summary.getGenerationIssues().get(0).getReasonCode());
        assertEquals(true, summary.getIsAttack());
        assertEquals(2, summary.getAttackBudget());
        assertEquals(true, summary.getEnablePrivacy());
        assertEquals(5, summary.getModelSemantics().getModeledAttackPointCount());
        assertEquals(dto.getModelSnapshot(), summary.getModelSnapshot());
        var runSummary = mapper.toRunSummaryDto(po, 1);
        assertEquals(1, runSummary.getCounterexampleCount());
        assertEquals(VerificationOutcome.VIOLATED, runSummary.getOutcome());
        assertEquals(false, runSummary.getModelComplete());
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
                .createdAt(LocalDateTime.now())
                .modelSnapshotJson(MODEL_SNAPSHOT_JSON)
                .outcome(VerificationOutcome.INCONCLUSIVE)
                .violatedSpecCount(1)
                .checkLogsJson("[\"[verification-inconclusive] result parsing was incomplete\"]")
                .build();

        VerificationTaskDto dto = mapper.toDto(po);

        assertEquals(VerificationOutcome.INCONCLUSIVE, dto.getOutcome());
        assertEquals(false, dto.getModelComplete());
    }

    @Test
    void missingModelSnapshotFailsClosed() {
        VerificationTaskPo po = VerificationTaskPo.builder()
                .id(9L)
                .userId(1L)
                .status(VerificationTaskPo.TaskStatus.COMPLETED)
                .createdAt(LocalDateTime.now())
                .outcome(VerificationOutcome.INCONCLUSIVE)
                .build();

        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));

        assertEquals("modelSnapshotJson", error.getField());
    }
}
