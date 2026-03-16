package cn.edu.nju.Iot_Verify.component.nusmv.fixer;

import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;

/**
 * Common interface for fix strategies (OCP — Open/Closed Principle).
 *
 * <p>Implementations: ParameterAdjustStrategy (§5.1), ConditionAdjustStrategy (§5.2),
 * DisableFixStrategy (fallback).</p>
 */
public interface FixStrategy {

    /**
     * Returns the strategy name used for dispatch (e.g., "parameter", "condition", "disable").
     */
    String name();

    /**
     * Whether this strategy requires a valid {@code violatedSpecIndex} (≥ 0) in the context.
     * Strategies that need spec negation (§5.1, §5.2) return {@code true};
     * strategies like "disable" that work without it return {@code false}.
     *
     * <p>Default is {@code true} for safety — strategies that don't need it must opt out.</p>
     */
    default boolean requiresViolatedSpec() {
        return true;
    }

    /**
     * Attempt to produce a fix suggestion for the violation described in {@code ctx}.
     *
     * @return a suggestion, or {@code null} if this strategy cannot fix the violation
     */
    FixSuggestionDto tryFix(FixContext ctx);
}
