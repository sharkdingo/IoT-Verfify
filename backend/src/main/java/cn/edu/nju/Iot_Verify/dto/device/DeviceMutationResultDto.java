package cn.edu.nju.Iot_Verify.dto.device;

import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.board.EnvironmentVariableChangeDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class DeviceMutationResultDto {
    private String operation;
    @Builder.Default
    private List<DeviceNodeDto> affectedDevices = List.of();
    @Builder.Default
    private List<DeviceNodeDto> currentNodes = List.of();
    @Builder.Default
    private List<BoardEnvironmentVariableDto> environmentVariables = List.of();
    @Builder.Default
    private List<EnvironmentVariableChangeDto> environmentChanges = List.of();
    @Builder.Default
    private List<SpecificationDto> currentSpecifications = List.of();
    private String previousLabel;
    private int updatedSpecificationCount;
    private int currentCount;
}
