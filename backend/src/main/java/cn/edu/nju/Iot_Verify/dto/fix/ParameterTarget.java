package cn.edu.nju.Iot_Verify.dto.fix;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

/** A numeric rule condition that can be targeted by a preferred fix range. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class ParameterTarget {
    private String targetId;
    private String attribute;
    private String relation;
    private String originalValue;
    private int lowerBound;
    private int upperBound;
    private String description;
}
