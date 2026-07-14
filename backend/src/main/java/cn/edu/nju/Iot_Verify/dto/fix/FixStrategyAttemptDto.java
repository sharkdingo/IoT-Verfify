package cn.edu.nju.Iot_Verify.dto.fix;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

/** User-facing execution status for one requested automatic-fix strategy. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FixStrategyAttemptDto {
    private String strategy;
    /**
     * VERIFIED, NOT_VERIFIED, NO_VERIFIED_SUGGESTION, TIMED_OUT, SKIPPED_TIMEOUT,
     * SKIPPED_NO_SPEC, SKIPPED_NO_FAULT_RULES, SKIPPED_UNSUPPORTED, or
     * SKIPPED_INCOMPLETE_SOURCE_MODEL.
     */
    private String status;
    private String reason;
}
