package cn.edu.nju.Iot_Verify.dto.fix;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FaultRuleDto {
    /** Rule index in the verification request's rule list (stable key). */
    private int ruleIndex;
    /** Rule database ID (nullable for unsaved rules). */
    private Long ruleId;
    private String ruleString;
    /** Counterexample step where this rule was triggered. */
    private int triggerStep;
    private String targetDevice;
    private String targetAction;
    private boolean conflicting;
    /** Index of the conflicting rule (nullable). */
    private Integer conflictWithRuleIndex;
    private String reason;
}
