package cn.edu.nju.Iot_Verify.repository.projection;

import java.time.LocalDateTime;

/** Closed projection for simulation history; requestJson is used only for integrity validation. */
public interface SimulationTraceSummaryProjection {

    Long getId();

    int getRequestedSteps();

    int getSteps();

    String getStatesJson();

    Integer getStateCount();

    String getLogsJson();

    String getGenerationIssuesJson();

    String getModelSnapshotJson();

    String getModelSemanticsJson();

    String getRequestJson();

    Boolean getIsAttack();

    Integer getAttackBudget();

    Boolean getEnablePrivacy();

    Integer getModeledDeviceAttackPointCount();

    Integer getModeledFalsifiableReadingDeviceCount();

    Integer getModeledAutomationLinkAttackPointCount();

    LocalDateTime getCreatedAt();
}
