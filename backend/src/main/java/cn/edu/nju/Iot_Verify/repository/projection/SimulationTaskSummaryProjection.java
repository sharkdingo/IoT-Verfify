package cn.edu.nju.Iot_Verify.repository.projection;

import cn.edu.nju.Iot_Verify.dto.model.TaskProgressStage;
import cn.edu.nju.Iot_Verify.dto.model.RunInitiator;
import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;

import java.time.LocalDateTime;

/** Closed task-inbox projection that excludes worker ownership and detail-only task payloads. */
public interface SimulationTaskSummaryProjection {

    Long getId();

    Long getUserId();

    RunInitiator getInitiator();

    SimulationTaskPo.TaskStatus getStatus();

    LocalDateTime getCreatedAt();

    LocalDateTime getStartedAt();

    LocalDateTime getCompletedAt();

    Long getProcessingTimeMs();

    Boolean getIsAttack();

    Integer getAttackBudget();

    Integer getModeledDeviceAttackPointCount();

    Integer getModeledFalsifiableReadingDeviceCount();

    Integer getModeledAutomationLinkAttackPointCount();

    Boolean getEnablePrivacy();

    String getModelSnapshotJson();

    String getModelSemanticsJson();

    Integer getRequestedSteps();

    Integer getSteps();

    Long getSimulationTraceId();

    String getCheckLogsJson();

    String getGenerationIssuesJson();

    String getErrorMessage();

    Integer getProgress();

    TaskProgressStage getProgressStage();
}
