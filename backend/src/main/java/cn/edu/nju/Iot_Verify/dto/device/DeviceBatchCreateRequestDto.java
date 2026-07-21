package cn.edu.nju.Iot_Verify.dto.device;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotEmpty;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Size;
import lombok.Data;

import java.util.ArrayList;
import java.util.List;

@Data
public class DeviceBatchCreateRequestDto {
    @NotEmpty(message = "At least one device is required")
    @Size(max = RequestLimits.MAX_DEVICES, message = "At most 100 devices can be created at once")
    private List<@Valid @NotNull(message = "Device item cannot be null") DeviceNodeDto> devices = new ArrayList<>();

    @Size(max = RequestLimits.MAX_ENVIRONMENT_VARIABLES, message = "At most 200 environment patches are allowed")
    private List<@Valid @NotNull(message = "Environment variable patch cannot be null")
            BoardEnvironmentVariableDto> environmentVariablePatches = new ArrayList<>();
}
