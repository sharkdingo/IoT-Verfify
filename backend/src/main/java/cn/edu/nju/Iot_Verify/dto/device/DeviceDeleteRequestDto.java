package cn.edu.nju.Iot_Verify.dto.device;

import jakarta.validation.constraints.NotBlank;
import lombok.Data;

@Data
public class DeviceDeleteRequestDto {
    @NotBlank(message = "Deletion impact token is required; request a fresh deletion preview first")
    private String impactToken;
}
