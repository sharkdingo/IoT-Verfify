package cn.edu.nju.Iot_Verify.dto.fix;

import cn.edu.nju.Iot_Verify.dto.model.ModelTokenSource;
import com.fasterxml.jackson.annotation.JsonIgnore;
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
    @JsonIgnore
    private int ruleIndex;
    /** Rule database ID (nullable for unsaved rules). */
    @JsonIgnore
    private Long ruleId;
    private String ruleString;
    /** One-based transition number in the counterexample where this rule fired. */
    private int transitionNumber;
    /** Internal model reference used by localization only. */
    @JsonIgnore
    private String targetDeviceId;
    private String targetDeviceLabel;
    /** Internal template API key used by localization only. */
    @JsonIgnore
    private String targetActionId;
    private String targetActionLabel;
    private boolean conflicting;
    /** Index of the conflicting rule (nullable). */
    @JsonIgnore
    private Integer conflictWithRuleIndex;
    private String conflictingRuleString;
    private String targetEndState;
    private String conflictingEndState;
    /** `TRIGGERED` or `CONFLICTING_END_STATES`; clients should localize from this code. */
    private String reasonCode;
    private String reason;
    @Builder.Default
    private ModelTokenSource modelTokenSource = ModelTokenSource.UNKNOWN;
}
