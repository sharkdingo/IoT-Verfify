package cn.edu.nju.Iot_Verify.dto.trace;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

/** User-facing snapshot of an automation rule that drove the transition into a trace state. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class TraceTriggeredRuleDto {
    /** Stable persisted rule identity when the submitted rule had one. */
    private String ruleId;

    /** Verification/simulation-time rule label; null when the user did not name the rule. */
    private String ruleLabel;
}
