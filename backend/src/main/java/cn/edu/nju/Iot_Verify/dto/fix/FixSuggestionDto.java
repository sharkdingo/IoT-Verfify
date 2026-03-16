package cn.edu.nju.Iot_Verify.dto.fix;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FixSuggestionDto {
    /** Strategy name: "parameter", "condition", "disable". */
    private String strategy;
    private String description;
    /** §5.1: Parameter threshold adjustments (for "parameter" strategy). */
    private List<ParameterAdjustment> parameterAdjustments;
    /** §5.2: Condition keep/remove adjustments (for "condition" strategy). */
    private List<ConditionAdjustment> conditionAdjustments;
    /** Indices of rules to disable (for "disable" strategy). */
    private List<Integer> disabledRuleIndices;
    /** Whether the fix was re-verified with NuSMV. */
    private boolean verified;
}
