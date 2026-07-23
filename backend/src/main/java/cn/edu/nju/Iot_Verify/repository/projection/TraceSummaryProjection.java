package cn.edu.nju.Iot_Verify.repository.projection;

import java.time.LocalDateTime;

/** Closed projection for verification trace summaries. */
public interface TraceSummaryProjection {

    Long getId();

    Long getVerificationTaskId();

    String getViolatedSpecId();

    String getViolatedSpecJson();

    Integer getStateCount();

    LocalDateTime getCreatedAt();
}
