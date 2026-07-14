package cn.edu.nju.Iot_Verify.dto.device;

import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.Size;
import lombok.Data;

@Data
public class DeviceRenameRequestDto {
    @NotBlank(message = "Device name is required")
    @Size(max = 100, message = "Device name must be at most 100 characters")
    private String label;
}
