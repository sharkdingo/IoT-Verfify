package cn.edu.nju.Iot_Verify.dto.device;

import jakarta.validation.constraints.NotBlank;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;
import lombok.ToString;

@Data
@NoArgsConstructor
@AllArgsConstructor
public class DeviceTemplateDeletionRequestDto {
    @NotBlank(message = "Template-deletion impact token is required")
    @ToString.Exclude
    private String impactToken;
}
