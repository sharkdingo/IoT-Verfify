package cn.edu.nju.Iot_Verify.dto.model;

import lombok.Builder;
import lombok.Value;

import java.time.LocalDateTime;

/** Lightweight impact snapshot that does not deserialize persisted evidence payloads. */
@Value
@Builder
public class RunDeletionImpactDto {

    Long runId;
    long evidenceCount;
    LocalDateTime createdAt;
    LocalDateTime completedAt;
}
