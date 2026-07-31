package cn.edu.nju.Iot_Verify.repository.projection;

import cn.edu.nju.Iot_Verify.dto.model.RunInitiator;
import java.time.LocalDateTime;

/** Closed history projection that excludes full state, request, and solver-output payloads. */
public interface SimulationTraceSummaryProjection {

    Long getId();

    RunInitiator getInitiator();

    int getRequestedSteps();

    int getSteps();

    Integer getStateCount();

    String getLogsJson();

    String getGenerationIssuesJson();

    String getModelSnapshotJson();

    String getModelSemanticsJson();

    Boolean getIsAttack();

    Integer getAttackBudget();

    Boolean getEnablePrivacy();

    Integer getModeledDeviceAttackPointCount();

    Integer getModeledFalsifiableReadingDeviceCount();

    Integer getModeledAutomationLinkAttackPointCount();

    LocalDateTime getCreatedAt();
}
