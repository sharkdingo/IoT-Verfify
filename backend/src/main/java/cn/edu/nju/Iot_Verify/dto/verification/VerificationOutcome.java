package cn.edu.nju.Iot_Verify.dto.verification;

/**
 * User-facing conclusion of a verification run.
 *
 * <p>A boolean pass flag cannot distinguish a real property violation from an
 * incomplete run. This enum is the single conclusion source across REST, AI tools,
 * and persisted async-task views.</p>
 */
public enum VerificationOutcome {
    SATISFIED,
    VIOLATED,
    INCONCLUSIVE;

    public static final String INCONCLUSIVE_LOG_MARKER = "[verification-inconclusive]";

    public boolean isModelComplete(int disabledRuleCount, int skippedSpecCount) {
        return this != INCONCLUSIVE && disabledRuleCount == 0 && skippedSpecCount == 0;
    }
}
