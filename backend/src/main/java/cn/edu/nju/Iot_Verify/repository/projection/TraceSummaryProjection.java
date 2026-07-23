package cn.edu.nju.Iot_Verify.repository.projection;

import java.time.LocalDateTime;

/** Closed projection for verification trace summaries. */
public interface TraceSummaryProjection {

    Long getId();

    Long getVerificationTaskId();

    String getViolatedSpecId();

    String getViolatedSpecJson();

    Boolean getIsAttack();

    Integer getAttackBudget();

    Boolean getEnablePrivacy();

    Integer getModeledDeviceAttackPointCount();

    Integer getModeledFalsifiableReadingDeviceCount();

    Integer getModeledAutomationLinkAttackPointCount();

    String getModelSemanticsJson();

    String getModelSnapshotJson();

    /** Internal frozen request used only to validate rule evidence; never serialized in the summary. */
    String getRequestJson();

    String getStatesJson();

    Integer getStateCount();

    LocalDateTime getCreatedAt();
}
