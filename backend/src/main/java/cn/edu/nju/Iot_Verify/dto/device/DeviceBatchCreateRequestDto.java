package cn.edu.nju.Iot_Verify.dto.device;

import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotEmpty;
import jakarta.validation.constraints.NotNull;
import lombok.Data;

import java.util.ArrayList;
import java.util.List;

@Data
public class DeviceBatchCreateRequestDto {
    @NotEmpty(message = "At least one device is required")
    private List<@Valid @NotNull(message = "Device item cannot be null") DeviceNodeDto> devices = new ArrayList<>();

    private List<@Valid @NotNull(message = "Environment variable patch cannot be null")
            BoardEnvironmentVariableDto> environmentVariablePatches = new ArrayList<>();
}
