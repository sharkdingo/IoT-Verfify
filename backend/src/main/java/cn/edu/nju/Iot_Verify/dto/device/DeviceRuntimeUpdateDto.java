package cn.edu.nju.Iot_Verify.dto.device;

import jakarta.validation.Valid;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

/** Compare-and-set replacement of a device-local runtime subresource. */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class DeviceRuntimeUpdateDto {

    @Valid
    @NotNull(message = "Expected runtime configuration is required")
    private DeviceRuntimeConfigDto expected;

    @Valid
    @NotNull(message = "Desired runtime configuration is required")
    private DeviceRuntimeConfigDto desired;
}
