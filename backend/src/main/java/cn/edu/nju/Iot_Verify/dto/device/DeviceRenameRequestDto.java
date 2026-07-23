package cn.edu.nju.Iot_Verify.dto.device;

import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.Size;
import lombok.Data;

@Data
public class DeviceRenameRequestDto {
    @NotBlank(message = "Device name is required")
    @Size(max = 255, message = "Device name must be at most 255 characters")
    private String label;

    @NotBlank(message = "Expected current device name is required")
    @Size(max = 255, message = "Expected current device name must be at most 255 characters")
    private String expectedLabel;
}
