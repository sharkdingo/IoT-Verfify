package cn.edu.nju.Iot_Verify.repository.projection;

import cn.edu.nju.Iot_Verify.dto.verification.VerificationOutcome;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;

import java.time.LocalDateTime;

/** Closed projection for completed verification history; excludes detail-only diagnostic columns. */
public interface VerificationRunSummaryProjection {

    Long getId();

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
}
