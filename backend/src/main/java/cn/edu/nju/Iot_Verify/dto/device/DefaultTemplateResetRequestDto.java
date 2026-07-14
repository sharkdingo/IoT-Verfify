package cn.edu.nju.Iot_Verify.dto.device;

import jakarta.validation.constraints.NotBlank;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@NoArgsConstructor
@AllArgsConstructor
public class DefaultTemplateResetRequestDto {
    @NotBlank(message = "Default-template reset impact token is required")
    private String impactToken;
}
