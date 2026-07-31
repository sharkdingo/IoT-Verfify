package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import cn.edu.nju.Iot_Verify.dto.device.DeviceLayoutDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelPlaybackSceneDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/** Enforces that replay layout and formal-model identity describe the same frozen device set. */
public final class ModelPlaybackSceneSnapshot {

    private ModelPlaybackSceneSnapshot() {}

    public static ModelPlaybackSceneDto canonicalize(
            List<DeviceNodeDto> playbackNodes,
            List<DeviceVerificationDto> devices,
            List<RuleDto> rules) {
        if (playbackNodes == null || devices == null) {
            throw new IllegalArgumentException("playbackNodes and submitted devices are required");
        }
        if (playbackNodes.isEmpty() && devices.isEmpty()) {
            return new ModelPlaybackSceneDto(List.of(), copyRules(rules, Set.of()));
        }
        if (playbackNodes.isEmpty() || devices.isEmpty() || playbackNodes.size() != devices.size()
                || playbackNodes.size() > RequestLimits.MAX_DEVICES) {
            throw new IllegalArgumentException("playbackNodes must match the submitted device count");
        }

        Map<String, DeviceVerificationDto> devicesById = new LinkedHashMap<>();
        for (DeviceVerificationDto device : devices) {
            String id = device == null ? null : trimToNull(device.getVarName());
            if (id == null || devicesById.putIfAbsent(id, device) != null) {
                throw new IllegalArgumentException("submitted device identities are missing or duplicate");
            }
        }

        Map<String, DeviceNodeDto> nodesById = new LinkedHashMap<>();
        for (DeviceNodeDto node : playbackNodes) {
            requireValidLayout(node);
            String canonicalId = DeviceNameNormalizer.normalize(node.getId().trim());
            DeviceVerificationDto device = devicesById.get(canonicalId);
            if (device == null || nodesById.containsKey(canonicalId)) {
                throw new IllegalArgumentException(
                        "playback node identities must match the submitted model devices");
            }
            String expectedLabel = trimToNull(device.getDeviceLabel());
            if (expectedLabel == null) expectedLabel = canonicalId;
            if (!Objects.equals(node.getTemplateName().trim(), device.getTemplateName().trim())
                    || !Objects.equals(node.getLabel().trim(), expectedLabel)) {
                throw new IllegalArgumentException(
                        "playback node labels and templates must match the submitted model devices");
            }
            nodesById.put(canonicalId, copyNode(node, canonicalId));
        }
        if (!nodesById.keySet().equals(devicesById.keySet())) {
            throw new IllegalArgumentException(
                    "playbackNodes must contain every submitted model device exactly once");
        }
        return new ModelPlaybackSceneDto(
                List.copyOf(nodesById.values()), copyRules(rules, nodesById.keySet()));
    }

    private static DeviceNodeDto copyNode(DeviceNodeDto source, String canonicalId) {
        DeviceNodeDto copy = new DeviceNodeDto();
        copy.setId(canonicalId);
        copy.setTemplateName(source.getTemplateName().trim());
        copy.setLabel(source.getLabel().trim());
        DeviceNodeDto.Position position = new DeviceNodeDto.Position();
        position.setX(source.getPosition().getX());
        position.setY(source.getPosition().getY());
        copy.setPosition(position);
        copy.setState(source.getState() == null ? "" : source.getState());
        copy.setWidth(source.getWidth());
        copy.setHeight(source.getHeight());
        copy.setCurrentStateTrust(source.getCurrentStateTrust());
        copy.setCurrentStatePrivacy(source.getCurrentStatePrivacy());
        copy.setVariables(copyVariables(source.getVariables()));
        copy.setPrivacies(copyPrivacies(source.getPrivacies()));
        return copy;
    }

    private static List<VariableStateDto> copyVariables(List<VariableStateDto> variables) {
        if (variables == null) return null;
        if (variables.size() > RequestLimits.MAX_DEVICE_VARIABLES) {
            throw new IllegalArgumentException("playback node contains too many variable values");
        }
        return variables.stream()
                .map(value -> {
                    if (value == null) {
                        throw new IllegalArgumentException("playback node contains a null variable value");
                    }
                    requireMaxLength(value.getName(), RequestLimits.MAX_IDENTIFIER_LENGTH,
                            "playback variable name");
                    requireMaxLength(value.getValue(), RequestLimits.MAX_VALUE_LENGTH,
                            "playback variable value");
                    requireMaxLength(value.getTrust(), 20, "playback variable trust");
                    return new VariableStateDto(value.getName(), value.getValue(), value.getTrust());
                })
                .toList();
    }

    private static List<PrivacyStateDto> copyPrivacies(List<PrivacyStateDto> privacies) {
        if (privacies == null) return null;
        if (privacies.size() > RequestLimits.MAX_DEVICE_PRIVACIES) {
            throw new IllegalArgumentException("playback node contains too many sensitivity values");
        }
        return privacies.stream()
                .map(value -> {
                    if (value == null) {
                        throw new IllegalArgumentException("playback node contains a null sensitivity value");
                    }
                    requireMaxLength(value.getName(), RequestLimits.MAX_IDENTIFIER_LENGTH,
                            "playback sensitivity name");
                    requireMaxLength(value.getPrivacy(), 20, "playback sensitivity label");
                    return new PrivacyStateDto(value.getName(), value.getPrivacy());
                })
                .toList();
    }

    private static List<RuleDto> copyRules(List<RuleDto> rules, Set<String> nodeIds) {
        if (rules == null) return List.of();
        return rules.stream().map(rule -> copyRule(rule, nodeIds)).toList();
    }

    private static RuleDto copyRule(RuleDto source, Set<String> nodeIds) {
        if (source == null || source.getConditions() == null || source.getConditions().isEmpty()
                || source.getCommand() == null) {
            throw new IllegalArgumentException("playback rules contain invalid structure");
        }
        List<RuleDto.Condition> conditions = source.getConditions().stream()
                .map(condition -> copyCondition(condition, nodeIds))
                .toList();
        RuleDto.Command command = source.getCommand();
        if (!nodeIds.contains(trimToNull(command.getDeviceName()))
                || trimToNull(command.getAction()) == null) {
            throw new IllegalArgumentException("playback rules reference an unknown device");
        }
        return RuleDto.builder()
                .id(source.getId())
                .userId(source.getUserId())
                .conditions(conditions)
                .command(RuleDto.Command.builder()
                        .deviceName(command.getDeviceName().trim())
                        .action(command.getAction().trim())
                        .contentDevice(command.getContentDevice())
                        .content(command.getContent())
                        .build())
                .ruleString(source.getRuleString())
                .createdAt(source.getCreatedAt())
                .build();
    }

    private static RuleDto.Condition copyCondition(
            RuleDto.Condition source, Set<String> nodeIds) {
        String deviceName = source == null ? null : trimToNull(source.getDeviceName());
        String attribute = source == null ? null : trimToNull(source.getAttribute());
        String targetType = source == null ? null : trimToNull(source.getTargetType());
        if (!nodeIds.contains(deviceName) || attribute == null || targetType == null) {
            throw new IllegalArgumentException("playback rules reference an unknown device");
        }
        String normalizedTargetType = targetType.toLowerCase(Locale.ROOT);
        if (!Set.of("api", "variable", "mode", "state").contains(normalizedTargetType)) {
            throw new IllegalArgumentException("playback rules contain an invalid condition type");
        }
        return RuleDto.Condition.builder()
                .deviceName(deviceName)
                .attribute(attribute)
                .targetType(normalizedTargetType)
                .relation(source.getRelation())
                .value(source.getValue())
                .build();
    }

    private static void requireValidLayout(DeviceNodeDto node) {
        if (node == null || trimToNull(node.getId()) == null
                || trimToNull(node.getTemplateName()) == null || trimToNull(node.getLabel()) == null
                || node.getPosition() == null || node.getPosition().getX() == null
                || node.getPosition().getY() == null
                || !Double.isFinite(node.getPosition().getX())
                || !Double.isFinite(node.getPosition().getY())
                || node.getWidth() == null || node.getWidth() < DeviceLayoutDto.MIN_WIDTH
                || node.getWidth() > DeviceLayoutDto.MAX_WIDTH
                || node.getHeight() == null || node.getHeight() < DeviceLayoutDto.MIN_HEIGHT
                || node.getHeight() > DeviceLayoutDto.MAX_HEIGHT) {
            throw new IllegalArgumentException("playbackNodes contain invalid visual layout data");
        }
    }

    private static String trimToNull(String value) {
        if (value == null) return null;
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }

    private static void requireMaxLength(String value, int maximum, String field) {
        if (value != null && value.length() > maximum) {
            throw new IllegalArgumentException(field + " exceeds its maximum length");
        }
    }
}
