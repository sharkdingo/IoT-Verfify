package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueReasonCode;
import cn.edu.nju.Iot_Verify.dto.model.TaskProgressStage;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskSummaryDto;
import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
import org.junit.jupiter.api.Test;

import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

class SimulationTaskMapperTest {

    private final SimulationTaskMapper mapper = new SimulationTaskMapper();
    private static final String MODEL_SNAPSHOT_JSON = "{\"capturedAt\":\"2026-07-12T09:30:00\","
            + "\"deviceCount\":2,\"ruleCount\":1,\"specificationCount\":0,"
            + "\"environmentVariableCount\":1,\"deviceTemplateCount\":2,\"templatesFrozen\":true}";

    @Test
    void mapsStructuredGenerationIssuesToTaskAndSummary() {
        SimulationTaskPo po = SimulationTaskPo.builder()
                .id(7L)
                .userId(1L)
                .status(SimulationTaskPo.TaskStatus.COMPLETED)
                .createdAt(LocalDateTime.now())
                .progress(80)
                .progressStage(TaskProgressStage.RUNNING_SIMULATION)
                .isAttack(true)
                .attackBudget(3)
                .modeledDeviceAttackPointCount(4)
                .modeledFalsifiableReadingDeviceCount(2)
                .modeledAutomationLinkAttackPointCount(2)
                .enablePrivacy(true)
                .modelSnapshotJson(MODEL_SNAPSHOT_JSON)
                .generationIssuesJson("[{\"issueType\":\"RULE_DISABLED\","
                        + "\"itemLabel\":\"When motion is detected, turn on the hall light\","
                        + "\"reasonCode\":\"RULE_UNRESOLVABLE_TRIGGER_CONDITION\","
                        + "\"reason\":\"The target action is not available on this device type.\"}]")
                .checkLogsJson("[]")
                .build();

        SimulationTaskDto task = mapper.toDto(po);
        SimulationTaskSummaryDto summary = mapper.toSummaryDto(po);

        assertEquals(1, task.getDisabledRuleCount());
        assertEquals(TaskProgressStage.RUNNING_SIMULATION, task.getProgressStage());
        assertEquals(true, task.getIsAttack());
        assertEquals(3, task.getAttackBudget());
        assertEquals(true, task.getEnablePrivacy());
        assertEquals(6, task.getModelSemantics().getModeledAttackPointCount());
        assertEquals(2, task.getModelSemantics().getModeledFalsifiableReadingDeviceCount());
        assertEquals(2, task.getModelSnapshot().getDeviceCount());
        assertEquals(0, task.getModelSnapshot().getSpecificationCount());
        assertEquals(true, task.getModelSnapshot().isTemplatesFrozen());
        assertFalse(task.getModelComplete());
        assertEquals("When motion is detected, turn on the hall light",
                task.getGenerationIssues().get(0).getItemLabel());
        assertEquals(ModelGenerationIssueReasonCode.RULE_UNRESOLVABLE_TRIGGER_CONDITION,
                task.getGenerationIssues().get(0).getReasonCode());
        assertEquals(task.getGenerationIssues(), summary.getGenerationIssues());
        assertEquals(1, summary.getDisabledRuleCount());
        assertEquals(TaskProgressStage.RUNNING_SIMULATION, summary.getProgressStage());
        assertEquals(true, summary.getIsAttack());
        assertEquals(3, summary.getAttackBudget());
        assertEquals(true, summary.getEnablePrivacy());
        assertEquals(4, summary.getModelSemantics().getModeledDeviceAttackPointCount());
        assertEquals(2, summary.getModelSemantics().getModeledAutomationLinkAttackPointCount());
        assertFalse(summary.getModelComplete());
        assertEquals(task.getModelSnapshot(), summary.getModelSnapshot());
    }
}
