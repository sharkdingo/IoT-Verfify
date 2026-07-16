package cn.edu.nju.Iot_Verify.component.fuzz;

import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;

public record FuzzSpecEligibility(
        SpecificationDto specification,
        boolean supported,
        String reasonCode,
        String reason) {
}
