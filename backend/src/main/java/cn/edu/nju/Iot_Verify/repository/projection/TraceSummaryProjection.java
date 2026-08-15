package cn.edu.nju.Iot_Verify.repository.projection;

import java.time.LocalDateTime;

/** Closed history projection that excludes full trace and frozen-request JSON. */
public interface TraceSummaryProjection {

    Long getId();

    Long getVerificationTaskId();

    String getViolatedSpecId();

    String getViolatedSpecJson();

    Integer getStateCount();

    /**
     * Whether {@code smvModelContent} is non-empty, computed in SQL. Selected as a flag rather than as
     * the column so a history list never loads tens of thousands of characters per row just to decide
     * whether a download button can succeed.
     */
    Boolean getHasSmvModel();

    LocalDateTime getCreatedAt();
}
