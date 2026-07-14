package cn.edu.nju.Iot_Verify.dto.fix;

import com.fasterxml.jackson.annotation.JsonIgnore;
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
    /** Internal trace-snapshot locator used only while applying the server-recomputed fix. */
    @JsonIgnore
    private int ruleIndex;
    /** Internal trace-snapshot locator used only while applying the server-recomputed fix. */
    @JsonIgnore
    private int conditionIndex;
    /** "remove" | "keep" | "add" */
    private String action;
    /** Attribute name of the condition */
    private String attribute;
    /** api | variable | mode | state */
    private String targetType;
    /** Human-readable description of the adjustment */
    private String description;
    /** User-facing rule snapshot; never used to locate the rule. */
    private String ruleDescription;
    /** User-facing device-instance label captured with the verification request. */
    private String deviceLabel;
    /** Internal model reference used only by the server when recomputing/applying an add operation. */
    @JsonIgnore
    private String deviceName;
    private String relation;
    private String value;
}
