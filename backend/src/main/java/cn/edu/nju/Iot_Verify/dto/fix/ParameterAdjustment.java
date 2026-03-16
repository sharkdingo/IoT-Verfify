package cn.edu.nju.Iot_Verify.dto.fix;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * §5.1 Rule Parameter Adjustment result: a numeric threshold change.
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class ParameterAdjustment {
    private int ruleIndex;
    private int conditionIndex;
    /** Attribute name, e.g. "temperature" */
    private String attribute;
    /** Relation operator, e.g. ">" */
    private String relation;
    /** Original threshold value, e.g. "30" */
    private String originalValue;
    /** New threshold value found by NuSMV, e.g. "25" */
    private String newValue;
    private int lowerBound;
    private int upperBound;
}
