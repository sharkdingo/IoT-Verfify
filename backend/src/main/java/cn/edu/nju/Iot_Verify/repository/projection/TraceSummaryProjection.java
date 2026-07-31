package cn.edu.nju.Iot_Verify.repository.projection;

import java.time.LocalDateTime;

/** Closed history projection that excludes full trace and frozen-request JSON. */
public interface TraceSummaryProjection {

    Long getId();

    Long getVerificationTaskId();

    String getViolatedSpecId();

    String getViolatedSpecJson();

    Integer getStateCount();

    LocalDateTime getCreatedAt();
}
