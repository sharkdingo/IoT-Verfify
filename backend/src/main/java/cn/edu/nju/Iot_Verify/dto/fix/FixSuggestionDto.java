package cn.edu.nju.Iot_Verify.dto.fix;

import com.fasterxml.jackson.annotation.JsonIgnore;
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
    /** Strategy name: "parameter", "condition", or "remove". */
    private String strategy;
    private String description;
    /** §5.1: Parameter threshold adjustments (for "parameter" strategy). */
    @Builder.Default
    private List<ParameterAdjustment> parameterAdjustments = List.of();
    /** §5.2: Condition keep/remove adjustments (for "condition" strategy). */
    @Builder.Default
    private List<ConditionAdjustment> conditionAdjustments = List.of();
    /** Internal positions of rules to remove (for the "remove" strategy). */
    @JsonIgnore
    private List<Integer> removedRuleIndices;
    /** Human-readable rules that would be permanently removed from the active board. */
    @Builder.Default
    private List<String> removedRuleDescriptions = List.of();
    /** Whether the fix was re-verified with NuSMV. */
    private boolean verified;
}
