package cn.edu.nju.Iot_Verify.component.fuzz.paper;

/**
 * Resolves the rule conditions that can establish the current transition conditions.
 *
 * <p>The returned condition belongs to the next solver level. Returning {@code null}
 * ends the predecessor chain.</p>
 */
@FunctionalInterface
public interface PaperPredecessorResolver {

    PaperCondition previousConditions(PaperCondition currentConditions, int currentLevel);

    static PaperPredecessorResolver none() {
        return (conditions, level) -> null;
    }
}
