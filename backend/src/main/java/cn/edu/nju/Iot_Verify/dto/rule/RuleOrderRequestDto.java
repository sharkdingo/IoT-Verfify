package cn.edu.nju.Iot_Verify.dto.rule;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import jakarta.validation.constraints.NotEmpty;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Positive;
import jakarta.validation.constraints.Size;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/** Compare-and-set replacement of the authenticated user's complete rule execution order. */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class RuleOrderRequestDto {

    @NotEmpty(message = "expectedRuleIds cannot be empty")
    @Size(max = RequestLimits.MAX_RULES, message = "At most 100 expected rules can be ordered")
    private List<@NotNull(message = "Expected rule id cannot be null")
            @Positive(message = "Expected rule id must be positive") Long> expectedRuleIds;

    @NotEmpty(message = "ruleIds cannot be empty")
    @Size(max = RequestLimits.MAX_RULES, message = "At most 100 rules can be ordered")
    private List<@NotNull(message = "Rule id cannot be null") @Positive(message = "Rule id must be positive") Long> ruleIds;
}
