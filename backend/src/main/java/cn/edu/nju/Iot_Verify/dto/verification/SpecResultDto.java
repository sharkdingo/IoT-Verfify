package cn.edu.nju.Iot_Verify.dto.verification;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * Result for one specification emitted to NuSMV.
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class SpecResultDto {
    /**
     * Stable SpecificationDto.id for the emitted specification.
     */
    private String specId;

    /**
     * Whether NuSMV reported the emitted specification as satisfied.
     */
    private boolean passed;

    /**
     * NuSMV expression that was checked for this specification.
     */
    private String expression;
}
