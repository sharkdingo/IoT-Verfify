package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;
import java.util.stream.Collectors;

/**
 * 辅助类：获取设备节点及其对应模板的详细信息
 * 用于规则推荐时获取设备的真实 API 和内部变量
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class DeviceInfoHelper {

    private final BoardStorageService boardStorageService;

    /**
     * 获取用户当前面板上的所有设备信息，包括模板详情
     */
    public List<DeviceInfo> getDevicesWithTemplateInfo(Long userId) {
        List<DeviceNodeDto> nodes = boardStorageService.getNodes(userId);
        if (nodes == null || nodes.isEmpty()) {
            return Collections.emptyList();
        }

        List<DeviceTemplateDto> templates = boardStorageService.getDeviceTemplates(userId);
        Map<String, DeviceTemplateDto> templateMap = templates.stream()
                .collect(Collectors.toMap(
                        DeviceTemplateDto::getName,
                        t -> t,
                        (existing, replacement) -> existing
                ));

        return nodes.stream()
                .filter(n -> n != null && n.getTemplateName() != null)
                .map(n -> {
                    DeviceTemplateDto template = templateMap.get(n.getTemplateName());
                    return new DeviceInfo(
                            n.getId(),
                            n.getLabel(),
                            n.getTemplateName(),
                            n.getState(),
                            extractVariables(template),
                            extractApis(template),
                            extractTransitions(template),
                            extractWorkingStates(template)
                    );
                })
                .collect(Collectors.toList());
    }

    /**
     * 提取模板中的内部变量
     */
    private List<VariableInfo> extractVariables(DeviceTemplateDto template) {
        if (template == null || template.getManifest() == null
                || template.getManifest().getInternalVariables() == null) {
            return Collections.emptyList();
        }

        return template.getManifest().getInternalVariables().stream()
                .map(v -> new VariableInfo(
                        v.getName(),
                        v.getDescription(),
                        v.getValues(),
                        v.getLowerBound(),
                        v.getUpperBound(),
                        v.getTrust(),
                        v.getPrivacy()
                ))
                .collect(Collectors.toList());
    }

    /**
     * 提取模板中的 API
     */
    private List<ApiInfo> extractApis(DeviceTemplateDto template) {
        if (template == null || template.getManifest() == null
                || template.getManifest().getApis() == null) {
            return Collections.emptyList();
        }

        return template.getManifest().getApis().stream()
                .map(a -> new ApiInfo(
                        a.getName(),
                        a.getDescription(),
                        a.getSignal(),
                        a.getStartState(),
                        a.getEndState(),
                        extractTriggerInfo(a),
                        extractAssignments(a)
                ))
                .collect(Collectors.toList());
    }

    private String extractTriggerInfo(DeviceTemplateDto.DeviceManifest.API api) {
        if (api.getTrigger() == null) return null;
        var t = api.getTrigger();
        return String.format("%s %s %s",
                t.getAttribute() != null ? t.getAttribute() : "",
                t.getRelation() != null ? t.getRelation() : "",
                t.getValue() != null ? t.getValue() : "");
    }

    private List<String> extractAssignments(DeviceTemplateDto.DeviceManifest.API api) {
        if (api.getAssignments() == null) return Collections.emptyList();
        return api.getAssignments().stream()
                .map(a -> String.format("%s=%s",
                        a.getAttribute() != null ? a.getAttribute() : "",
                        a.getValue() != null ? a.getValue() : ""))
                .collect(Collectors.toList());
    }

    /**
     * 提取模板中的状态转换
     */
    private List<TransitionInfo> extractTransitions(DeviceTemplateDto template) {
        if (template == null || template.getManifest() == null
                || template.getManifest().getTransitions() == null) {
            return Collections.emptyList();
        }

        return template.getManifest().getTransitions().stream()
                .map(t -> new TransitionInfo(
                        t.getName(),
                        t.getDescription(),
                        t.getStartState(),
                        t.getEndState(),
                        t.getSignal()
                ))
                .collect(Collectors.toList());
    }

    /**
     * 提取工作状态
     */
    private List<String> extractWorkingStates(DeviceTemplateDto template) {
        if (template == null || template.getManifest() == null
                || template.getManifest().getWorkingStates() == null) {
            return Collections.emptyList();
        }
        return template.getManifest().getWorkingStates().stream()
                .map(DeviceTemplateDto.DeviceManifest.WorkingState::getName)
                .collect(Collectors.toList());
    }

    /**
     * 设备信息数据结构
     */
    public record DeviceInfo(
            String nodeId,
            String label,
            String templateName,
            String currentState,
            List<VariableInfo> variables,
            List<ApiInfo> apis,
            List<TransitionInfo> transitions,
            List<String> workingStates
    ) {}

    /**
     * 变量信息
     */
    public record VariableInfo(
            String name,
            String description,
            List<String> values,
            Integer lowerBound,
            Integer upperBound,
            String trust,
            String privacy
    ) {}

    /**
     * API 信息
     */
    public record ApiInfo(
            String name,
            String description,
            Boolean signal,
            String startState,
            String endState,
            String triggerInfo,
            List<String> assignments
    ) {}

    /**
     * 转换信息
     */
    public record TransitionInfo(
            String name,
            String description,
            String startState,
            String endState,
            Boolean signal
    ) {}
}

