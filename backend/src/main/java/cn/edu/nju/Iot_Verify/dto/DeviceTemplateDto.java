package cn.edu.nju.Iot_Verify.dto;

import cn.edu.nju.Iot_Verify.dto.manifest.DeviceManifest;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import lombok.Data;

@Data
public class DeviceTemplateDto {

    private String id;

    @NotBlank(message = "Template name is required")
    private String name;

    @Valid
    private DeviceManifest manifest;
}
