package cn.edu.nju.Iot_Verify.repository.projection;

import cn.edu.nju.Iot_Verify.dto.model.TaskProgressStage;
import cn.edu.nju.Iot_Verify.dto.model.RunInitiator;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationOutcome;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;

import java.time.LocalDateTime;

/** Closed task-inbox projection that excludes detail-only request, log, result, and solver output. */
public interface VerificationTaskSummaryProjection {

    Long getId();

    Long getUserId();

    RunInitiator getInitiator();

    VerificationTaskPo.TaskStatus getStatus();

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

    VerificationOutcome getOutcome();

    Integer getViolatedSpecCount();

    Integer getDisabledRuleCount();

    Integer getSkippedSpecCount();

    String getGenerationIssuesJson();

    String getErrorMessage();

    Integer getProgress();

    TaskProgressStage getProgressStage();
}
