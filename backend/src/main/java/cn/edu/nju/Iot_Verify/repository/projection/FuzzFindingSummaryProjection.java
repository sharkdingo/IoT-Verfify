package cn.edu.nju.Iot_Verify.repository.projection;

import java.time.LocalDateTime;

/** Lightweight history projection that excludes every finding LONGTEXT column. */
public interface FuzzFindingSummaryProjection {

    Long getId();

    Long getUserId();

    Long getFuzzTaskId();

    String getViolatedSpecId();

    Integer getFirstViolationStep();

    Long getSeed();

    Integer getStateCount();

    LocalDateTime getCreatedAt();
}
