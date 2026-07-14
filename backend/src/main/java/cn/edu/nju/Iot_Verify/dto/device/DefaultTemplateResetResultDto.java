package cn.edu.nju.Iot_Verify.dto.device;

import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.board.EnvironmentVariableChangeDto;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class DefaultTemplateResetResultDto {
    private String operation;
    private String impactToken;
    private boolean canApply;
    @Builder.Default
    private List<DefaultTemplateResetChangeDto> templateChanges = List.of();
    @Builder.Default
    private List<DefaultTemplateAffectedDeviceDto> affectedDevices = List.of();
    @Builder.Default
    private List<DefaultTemplateResetBlockerDto> blockers = List.of();
    @Builder.Default
    private List<EnvironmentVariableChangeDto> environmentChanges = List.of();
    @Builder.Default
    private List<DeviceTemplateDto> currentTemplates = List.of();
    @Builder.Default
    private List<BoardEnvironmentVariableDto> environmentVariables = List.of();
}
