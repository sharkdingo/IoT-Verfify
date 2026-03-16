package cn.edu.nju.Iot_Verify.dto.fix;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * §5.2 Triggering Condition Adjustment result: keep, remove, or add a sub-condition.
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class ConditionAdjustment {
    private int ruleIndex;
    private int conditionIndex;
    /** "remove" | "keep" | "add" */
    private String action;
    /** Attribute name of the condition */
    private String attribute;
    /** Human-readable description of the adjustment */
    private String description;
    // Fields below populated only when action="add"
    private String deviceName;
    private String relation;
    private String value;
}
