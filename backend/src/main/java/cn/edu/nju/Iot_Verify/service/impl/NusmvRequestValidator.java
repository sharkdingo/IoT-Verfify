package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvRelationUtils;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.ValidationException;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

final class NusmvRequestValidator {

    private NusmvRequestValidator() {
    }

    static void validateDevices(List<DeviceVerificationDto> devices, Map<String, String> errors) {
        for (int i = 0; i < devices.size(); i++) {
            DeviceVerificationDto device = devices.get(i);
            String prefix = "devices[" + i + "]";
            requireText(errors, prefix + ".varName", device.getVarName(), "Device varName is required");
            requireText(errors, prefix + ".templateName", device.getTemplateName(), "Template name is required");
            rejectNullItems(errors, prefix + ".variables", device.getVariables(), "Variable item cannot be null");
            rejectNullItems(errors, prefix + ".privacies", device.getPrivacies(), "Privacy item cannot be null");
        }
    }

    static void validateRules(List<RuleDto> rules, Map<String, String> errors) {
        for (int i = 0; i < rules.size(); i++) {
            RuleDto rule = rules.get(i);
            String prefix = "rules[" + i + "]";
            if (rule.getConditions() != null) {
                rejectNullItems(errors, prefix + ".conditions",
                        rule.getConditions(), "Condition item cannot be null");
            }
            RuleDto.Command command = rule.getCommand();
            if (command == null) {
                putError(errors, prefix + ".command", "Command cannot be null");
                continue;
            }
            requireText(errors, prefix + ".command.deviceName",
                    command.getDeviceName(), "Command device name is required");
            requireText(errors, prefix + ".command.action",
                    command.getAction(), "Command action is required");
        }
    }

    static void validateSpecifications(List<SpecificationDto> specs, Map<String, String> errors) {
        for (int i = 0; i < specs.size(); i++) {
            SpecificationDto spec = specs.get(i);
            String prefix = "specs[" + i + "]";
            requireText(errors, prefix + ".id", spec.getId(), "Specification ID is required");
            validateTemplateId(spec.getTemplateId(), prefix + ".templateId", errors);
            validateConditionList(spec.getAConditions(), prefix + ".aConditions", "a", errors);
            validateConditionList(spec.getIfConditions(), prefix + ".ifConditions", "if", errors);
            validateConditionList(spec.getThenConditions(), prefix + ".thenConditions", "then", errors);
        }
    }

    static Map<String, String> newErrors() {
        return new LinkedHashMap<>();
    }

    static void throwIfErrors(Map<String, String> errors) {
        if (!errors.isEmpty()) {
            throw new ValidationException(errors);
        }
    }

    private static void validateTemplateId(String templateId, String field, Map<String, String> errors) {
        if (!hasText(templateId)) {
            putError(errors, field, "Template ID is required");
            return;
        }
        if (!templateId.matches("^[1-7]$")) {
            putError(errors, field, "Template ID must be one of 1, 2, 3, 4, 5, 6, 7");
        }
    }

    private static void validateConditionList(List<SpecConditionDto> conditions,
                                              String field,
                                              String expectedSide,
                                              Map<String, String> errors) {
        if (conditions == null) {
            putError(errors, field, conditionListNullMessage(expectedSide));
            return;
        }
        for (int i = 0; i < conditions.size(); i++) {
            SpecConditionDto condition = conditions.get(i);
            String prefix = field + "[" + i + "]";
            if (condition == null) {
                putError(errors, prefix, conditionItemNullMessage(expectedSide));
                continue;
            }
            if (!hasText(condition.getDeviceId()) && !hasText(condition.getDeviceLabel())) {
                putError(errors, prefix + ".deviceId", "Device reference is required for spec condition");
            }
            validateTargetType(condition.getTargetType(), prefix + ".targetType", errors);
            requireText(errors, prefix + ".key", condition.getKey(), "Key is required for spec condition");
            validateRelation(condition.getRelation(), prefix + ".relation", errors);
            requireText(errors, prefix + ".value", condition.getValue(), "Value is required for spec condition");
        }
    }

    private static void validateTargetType(String targetType, String field, Map<String, String> errors) {
        if (!hasText(targetType)) {
            putError(errors, field, "Target type is required for spec condition");
            return;
        }
        String normalized = targetType.trim().toLowerCase();
        if (!List.of("state", "variable", "api", "trust", "privacy").contains(normalized)) {
            putError(errors, field, "targetType must be one of: state, variable, api, trust, privacy");
        }
    }

    private static void validateRelation(String relation, String field, Map<String, String> errors) {
        if (!hasText(relation)) {
            putError(errors, field, "Relation is required for spec condition");
            return;
        }
        String normalized = SmvRelationUtils.normalizeRelation(relation);
        if (!SmvRelationUtils.isSupportedRelation(normalized)) {
            putError(errors, field, "Relation must be one of =, !=, >, >=, <, <=, in, not_in, not in");
        }
    }

    private static <T> void rejectNullItems(Map<String, String> errors,
                                            String field,
                                            List<T> values,
                                            String message) {
        if (values == null) {
            return;
        }
        for (int i = 0; i < values.size(); i++) {
            if (values.get(i) == null) {
                putError(errors, field + "[" + i + "]", message);
            }
        }
    }

    private static void requireText(Map<String, String> errors, String field, String value, String message) {
        if (!hasText(value)) {
            putError(errors, field, message);
        }
    }

    private static void putError(Map<String, String> errors, String field, String message) {
        errors.putIfAbsent(field, message);
    }

    private static boolean hasText(String value) {
        return value != null && !value.isBlank();
    }

    private static String conditionListNullMessage(String side) {
        return switch (side) {
            case "a" -> "A-conditions cannot be null";
            case "if" -> "If-conditions cannot be null";
            case "then" -> "Then-conditions cannot be null";
            default -> "Conditions cannot be null";
        };
    }

    private static String conditionItemNullMessage(String side) {
        return switch (side) {
            case "a" -> "A-condition item cannot be null";
            case "if" -> "If-condition item cannot be null";
            case "then" -> "Then-condition item cannot be null";
            default -> "Condition item cannot be null";
        };
    }
}
