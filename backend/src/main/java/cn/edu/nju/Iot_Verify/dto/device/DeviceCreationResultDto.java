package cn.edu.nju.Iot_Verify.dto.device;

import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.board.EnvironmentVariableChangeDto;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.List;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class DeviceCreationResultDto {

    private DeviceNodeDto device;
    private String initialStateSource;

    @Builder.Default
    private List<String> defaultsApplied = new ArrayList<>();

    @Builder.Default
    private List<String> warnings = new ArrayList<>();

    @Builder.Default
    private List<BoardEnvironmentVariableDto> environmentVariables = new ArrayList<>();

    @Builder.Default
    private List<EnvironmentVariableChangeDto> environmentChanges = new ArrayList<>();
}
