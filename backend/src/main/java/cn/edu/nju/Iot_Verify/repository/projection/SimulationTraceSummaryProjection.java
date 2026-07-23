package cn.edu.nju.Iot_Verify.repository.projection;

import java.time.LocalDateTime;

/** Closed projection for simulation history; excludes request snapshots and raw NuSMV output. */
public interface SimulationTraceSummaryProjection {

    Long getId();

    int getRequestedSteps();

    int getSteps();

    Integer getStateCount();

    String getLogsJson();

    String getGenerationIssuesJson();

    String getModelSnapshotJson();

    Boolean getIsAttack();

    Integer getAttackBudget();

    Boolean getEnablePrivacy();

    LocalDateTime getCreatedAt();
}
