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
     * VERIFIED, NOT_VERIFIED, NO_VERIFIED_SUGGESTION, FAILED_MODEL_GENERATION,
     * FAILED_SOLVER_EXECUTION, SEARCH_BUDGET_EXHAUSTED, TIMED_OUT, SKIPPED_TIMEOUT,
     * SKIPPED_NO_SPEC, SKIPPED_NO_PARAMETERIZABLE_VALUES, SKIPPED_NO_FAULT_RULES,
     * SKIPPED_UNSUPPORTED, or SKIPPED_INCOMPLETE_SOURCE_MODEL.
     */
    private String status;
    private String reason;
    /** Main candidate-search attempts consumed by this strategy, when it ran. */
    private Integer attemptsUsed;
    /** Configured main candidate-search limit for this strategy, when it ran. */
    private Integer attemptLimit;
}
