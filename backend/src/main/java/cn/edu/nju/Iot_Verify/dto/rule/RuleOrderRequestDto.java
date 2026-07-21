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

/** Complete desired execution order for the authenticated user's current rules. */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class RuleOrderRequestDto {

    @NotEmpty(message = "ruleIds cannot be empty")
    @Size(max = RequestLimits.MAX_RULES, message = "At most 100 rules can be ordered")
    private List<@NotNull(message = "Rule id cannot be null") @Positive(message = "Rule id must be positive") Long> ruleIds;
}
