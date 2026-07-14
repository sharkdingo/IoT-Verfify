package cn.edu.nju.Iot_Verify.dto.board;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;

import java.util.List;

/**
 * One persisted board-semantic snapshot captured under the user/database write lock.
 * Layout is intentionally excluded because it does not affect the NuSMV model.
 */
public record BoardSemanticSnapshotDto(
        List<DeviceNodeDto> nodes,
        List<BoardEnvironmentVariableDto> environmentVariables,
        List<RuleDto> rules,
        List<SpecificationDto> specifications,
        List<DeviceTemplateDto> deviceTemplates) {

    public BoardSemanticSnapshotDto {
        nodes = immutable(nodes);
        environmentVariables = immutable(environmentVariables);
        rules = immutable(rules);
        specifications = immutable(specifications);
        deviceTemplates = immutable(deviceTemplates);
    }

    private static <T> List<T> immutable(List<T> values) {
        return values == null || values.isEmpty() ? List.of() : List.copyOf(values);
    }
}
