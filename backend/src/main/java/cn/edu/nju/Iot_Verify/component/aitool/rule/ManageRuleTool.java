package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.component.aitool.AiDestructiveActionGuard;
import cn.edu.nju.Iot_Verify.component.aitool.BoardSemanticValidator;
import cn.edu.nju.Iot_Verify.dto.board.CollectionMutationResultDto;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvRelationUtils;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

@Slf4j
@Component
public class ManageRuleTool extends AbstractAiTool {

    private static final Set<String> TARGET_TYPES = Set.of("api", "variable", "mode", "state");
    private static final Set<String> ENUM_RELATIONS = Set.of("=", "!=", "in", "not in");

    private final BoardStorageService boardStorageService;
    private final AiDestructiveActionGuard destructiveActionGuard;

    public ManageRuleTool(BoardStorageService boardStorageService,
                          ObjectMapper objectMapper,
                          AiDestructiveActionGuard destructiveActionGuard) {
        super(objectMapper);
        this.boardStorageService = boardStorageService;
        this.destructiveActionGuard = destructiveActionGuard;
    }

    @Override
    public String getName() {
        return "manage_rule";
    }

    @Override
    public LlmToolSpec getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("action", Map.of(
                "type", "string",
                "enum", List.of("add", "delete"),
                "description", "Action to perform: 'add' to create a new rule, 'delete' to remove an existing rule."
        ));

        props.put("conditions", Map.of(
                "type", "array",
                "description", "Required for 'add'. Each condition: {deviceId, deviceLabel?, attribute, targetType, relation, value}. deviceId is the canonical board device id returned by board_overview or recommend_rules; deviceLabel is display-only. targetType=api is an event signal: attribute must be a Signal=true API and relation/value must be omitted. targetType=state/mode/variable requires relation and value; all value conditions support =, !=, in, not in; numeric variables additionally support >, <, >=, <=.",
                "items", Map.of(
                        "type", "object",
                        "properties", Map.of(
                                "deviceId", Map.of("type", "string"),
                                "deviceLabel", Map.of("type", "string", "description", "Optional display snapshot; ignored for identity resolution."),
                                "attribute", Map.of("type", "string"),
                                "targetType", Map.of("type", "string", "enum", List.of("api", "variable", "mode", "state")),
                                "relation", Map.of("type", "string"),
                                "value", Map.of("type", "string")
                        ),
                        "required", List.of("deviceId", "attribute", "targetType"),
                        "additionalProperties", false
                )
        ));

        props.put("command", Map.of(
                "type", "object",
                "description", "Required for 'add'. The action to execute when conditions are met. deviceId/contentDevice must be canonical board device ids; labels are display-only.",
                "properties", Map.of(
                        "deviceId", Map.of("type", "string"),
                        "deviceLabel", Map.of("type", "string", "description", "Optional display snapshot; ignored for identity resolution."),
                        "action", Map.of("type", "string"),
                        "contentDevice", Map.of("type", "string"),
                        "contentDeviceLabel", Map.of("type", "string", "description", "Optional display snapshot; ignored for identity resolution."),
                        "content", Map.of("type", "string")
                ),
                "required", List.of("deviceId", "action"),
                "additionalProperties", false
        ));

        props.put("label", Map.of(
                "type", "string",
                "description", "Optional user-facing rule name. It does not define behavior. If omitted, the backend generates a readable label from the typed conditions and command."
        ));

        props.put("ruleId", Map.of(
                "type", "integer",
                "description", "Required for 'delete'. The ID of the rule to delete (from list_rules result)."
        ));
        props.put("confirmed", Map.of(
                "type", "boolean",
                "description", "For delete: use false to preview the exact rule without changing it; use true only in a later turn after the user explicitly confirms that preview. Ignored for add."
        ));
        props.put("impactToken", Map.of(
                "type", "string",
                "description", "For delete with confirmed=true, copy the opaque impactToken from the latest preview."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, List.of("action")
        );

        return LlmToolSpec.of(getName(), "Add an automation rule, or preview/delete one through explicit two-turn confirmation. Use list_rules before deleting.", schema);
    }

    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }
            requireOnlyFields(args, "arguments", Set.of(
                    "action", "conditions", "command", "label", "ruleId", "confirmed", "impactToken"));
            String action = requiredTextField(args, "action", "arguments").toLowerCase(Locale.ROOT);

            return switch (action) {
                case "add" -> executeAdd(userId, args);
                case "delete" -> executeDelete(userId, args);
                default -> errorJson("Unknown action: " + action + ". Use 'add' or 'delete'.",
                        "VALIDATION_ERROR", 400);
            };
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
        } catch (ServiceUnavailableException e) {
            log.warn("manage_rule busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("manage_rule business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("manage_rule failed", e);
            return errorJson("Rule operation failed. Please check parameters and retry.",
                    "INTERNAL_ERROR", 500);
        }
    }

    private String executeAdd(Long userId, JsonNode args) throws Exception {
        requireOnlyFields(args, "arguments", Set.of("action", "conditions", "command", "label"));
        JsonNode conditionsNode = args.path("conditions");
        JsonNode commandNode = args.path("command");
        List<DeviceNodeDto> nodes = safeList(boardStorageService.getNodes(userId));
        Set<String> deviceIds = getDeviceIds(nodes);
        Map<String, String> labelsById = labelsById(nodes);
        BoardSemanticValidator.BoardContext semanticContext = BoardSemanticValidator.context(
                nodes,
                safeList(boardStorageService.getDeviceTemplates(userId))
        );

        if (conditionsNode.isMissingNode() || !conditionsNode.isArray() || conditionsNode.isEmpty()) {
            return errorJson("'conditions' array is required for add action.",
                    "VALIDATION_ERROR", 400);
        }
        if (commandNode.isMissingNode() || !commandNode.isObject()) {
            return errorJson("'command' object is required for add action.",
                    "VALIDATION_ERROR", 400);
        }

        List<RuleDto.Condition> conditions = new ArrayList<>();
        int index = 0;
        for (JsonNode cn : conditionsNode) {
            String conditionPath = "arguments.conditions[" + index + "]";
            requireOnlyFields(cn, conditionPath, Set.of(
                    "deviceId", "deviceLabel", "attribute", "targetType", "relation", "value"));
            String deviceName = nullableTextField(cn, "deviceId", conditionPath);
            String attribute = nullableTextField(cn, "attribute", conditionPath);
            if (deviceName == null || attribute == null) {
                return errorJson("Condition " + (index + 1) + " must include non-empty 'deviceId' and 'attribute'.",
                        "VALIDATION_ERROR", 400);
            }

            String relationInput = nullableTextField(cn, "relation", conditionPath);
            String relation = normalizeRelation(relationInput);
            String value = nullableTextField(cn, "value", conditionPath);
            String targetTypeInput = nullableTextField(cn, "targetType", conditionPath);
            String targetType = normalizeTargetType(targetTypeInput);

            if (targetTypeInput == null) {
                return errorJson("Condition " + (index + 1) + " must include non-empty 'targetType'.",
                        "VALIDATION_ERROR", 400);
            }
            if (targetType == null) {
                return errorJson("Unsupported targetType '" + targetTypeInput + "' in condition " + (index + 1)
                        + ". Allowed: api, variable, mode, state.",
                        "VALIDATION_ERROR", 400);
            }
            if (!deviceIds.contains(deviceName)) {
                return errorJson("Unknown deviceId '" + deviceName + "' in condition " + (index + 1)
                        + ". Use a canonical id returned by board_overview.",
                        "VALIDATION_ERROR", 400);
            }

            if (relationInput != null && relation == null) {
                return errorJson("Unsupported relation '" + relationInput + "' in condition " + (index + 1)
                        + ". Allowed: =, !=, >, <, >=, <=, in, not in.",
                        "VALIDATION_ERROR", 400);
            }

            if ("api".equals(targetType)) {
                if (relation != null || value != null) {
                    return errorJson("API signal condition " + (index + 1) + " must not include relation or value.",
                            "VALIDATION_ERROR", 400);
                }
            } else {
                if (relation == null || value == null) {
                    return errorJson("Condition relation and value are required for targetType '" + targetType
                            + "' in condition " + (index + 1) + ".",
                            "VALIDATION_ERROR", 400);
                }
            }

            if (("in".equals(relation) || "not in".equals(relation)) && isEmptyValueList(value)) {
                return errorJson("Condition value list cannot be empty for relation '" + relation
                        + "' in condition " + (index + 1) + ".",
                        "VALIDATION_ERROR", 400);
            }

            if (("state".equals(targetType) || "mode".equals(targetType))
                    && !ENUM_RELATIONS.contains(relation)) {
                return errorJson("Condition targetType '" + targetType
                                + "' only supports =, !=, in, not in. Invalid condition: " + (index + 1),
                        "VALIDATION_ERROR", 400);
            }

            RuleDto.Condition condition = RuleDto.Condition.builder()
                    .deviceName(deviceName)
                    .attribute(attribute)
                    .targetType(targetType)
                    .relation(relation)
                    .value(value)
                    .build();
            String semanticError = BoardSemanticValidator.validateRuleCondition(semanticContext, condition, index);
            if (semanticError != null) {
                return errorJson(semanticError, "VALIDATION_ERROR", 400);
            }
            conditions.add(condition);
            index++;
        }

        requireOnlyFields(commandNode, "arguments.command", Set.of(
                "deviceId", "deviceLabel", "action", "contentDevice", "contentDeviceLabel", "content"));
        String commandDeviceName = nullableTextField(commandNode, "deviceId", "arguments.command");
        String commandAction = nullableTextField(commandNode, "action", "arguments.command");
        if (commandDeviceName == null || commandAction == null) {
            return errorJson("Command must include non-empty 'deviceId' and 'action'.",
                    "VALIDATION_ERROR", 400);
        }
        if (!deviceIds.contains(commandDeviceName)) {
            return errorJson("Unknown command deviceId '" + commandDeviceName
                            + "'. Use a canonical id returned by board_overview.",
                    "VALIDATION_ERROR", 400);
        }

        String contentDevice = nullableTextField(commandNode, "contentDevice", "arguments.command");
        if (contentDevice != null && !deviceIds.contains(contentDevice)) {
            return errorJson("Unknown command contentDevice '" + contentDevice + "'. Use the board device node id.",
                    "VALIDATION_ERROR", 400);
        }

        RuleDto.Command command = RuleDto.Command.builder()
                .deviceName(commandDeviceName)
                .action(commandAction)
                .contentDevice(contentDevice)
                .content(nullableTextField(commandNode, "content", "arguments.command"))
                .build();
        String commandSemanticError = BoardSemanticValidator.validateRuleCommand(semanticContext, command);
        if (commandSemanticError != null) {
            return errorJson(commandSemanticError, "VALIDATION_ERROR", 400);
        }

        String ruleString = nullableTextField(args, "label", "arguments");
        if (ruleString == null) {
            ruleString = buildRuleString(conditions, command, labelsById);
        }

        RuleDto newRule = RuleDto.builder()
                .userId(userId)
                .conditions(conditions)
                .command(command)
                .ruleString(ruleString)
                .build();

        CollectionMutationResultDto<RuleDto> mutation = boardStorageService.addRule(userId, newRule);

        Map<String, Object> response = new LinkedHashMap<>();
        response.put("message", "Rule created at the end of the execution order. It has not been formally verified.");
        response.put("operation", "created");
        response.put("verificationStatus", "NOT_VERIFIED");
        response.put("executionOrder", mutation.getCurrentCount());
        response.put("rule", RuleToolPresenter.present(mutation.getAffectedItem(), nodes));
        response.put("totalRules", mutation.getCurrentCount());
        return successJson(response, "Rule created but not formally verified.");
    }

    private String executeDelete(Long userId, JsonNode args) throws Exception {
        requireOnlyFields(args, "arguments", Set.of("action", "ruleId", "confirmed", "impactToken"));
        long ruleId = positiveLongArg(args, "ruleId");
        RuleDto target = safeList(boardStorageService.getRules(userId)).stream()
                .filter(rule -> rule != null && java.util.Objects.equals(rule.getId(), ruleId))
                .findFirst()
                .orElse(null);
        if (target == null) {
            return errorJson("Rule not found: " + ruleId, "NOT_FOUND", 404);
        }

        Object presentedRule = RuleToolPresenter.present(
                target, safeList(boardStorageService.getNodes(userId)));
        Map<String, Object> bindingSnapshot = Map.of("rule", presentedRule);
        boolean confirmed = booleanArg(args, "confirmed", false);
        if (!confirmed || !UserContextHolder.isDestructiveActionConfirmed()) {
            String impactToken = destructiveActionGuard.issue(
                    userId, getName(), Long.toString(ruleId), bindingSnapshot, null);
            Map<String, Object> preview = new LinkedHashMap<>();
            preview.put("message", "No changes were made. Explicit user confirmation is required before deleting this rule.");
            preview.put("operation", "preview");
            preview.put("requiresUserConfirmation", true);
            preview.put("rule", presentedRule);
            preview.put("impactToken", impactToken);
            return readOnlySuccessJson(preview, "Rule deletion preview unavailable.");
        }

        String impactToken = requiredTextField(args, "impactToken", "arguments");
        AiDestructiveActionGuard.ConsumeResult confirmation = destructiveActionGuard.consume(
                userId, getName(), Long.toString(ruleId), impactToken, bindingSnapshot);
        if (!confirmation.approved()) {
            String freshToken = destructiveActionGuard.issue(
                    userId, getName(), Long.toString(ruleId), bindingSnapshot, null);
            return errorJson(confirmation.message(), confirmation.errorCode(), 409, Map.of(
                    "requiresUserConfirmation", true,
                    "currentPreview", Map.of(
                            "operation", "preview",
                            "rule", presentedRule,
                            "impactToken", freshToken)));
        }

        CollectionMutationResultDto<RuleDto> mutation;
        try {
            mutation = boardStorageService.removeRuleIfUnchanged(userId, ruleId, target);
        } catch (ConflictException conflict) {
            RuleDto current = safeList(boardStorageService.getRules(userId)).stream()
                    .filter(rule -> rule != null && java.util.Objects.equals(rule.getId(), ruleId))
                    .findFirst()
                    .orElse(null);
            if (current == null) {
                return errorJson("Rule not found: " + ruleId, "NOT_FOUND", 404);
            }
            Object currentPresentation = RuleToolPresenter.present(
                    current, safeList(boardStorageService.getNodes(userId)));
            Map<String, Object> currentBinding = Map.of("rule", currentPresentation);
            String freshToken = destructiveActionGuard.issue(
                    userId, getName(), Long.toString(ruleId), currentBinding, null);
            return errorJson(conflict.getMessage(), "CONFIRMATION_STALE", 409, Map.of(
                    "requiresUserConfirmation", true,
                    "currentPreview", Map.of(
                            "operation", "preview",
                            "rule", currentPresentation,
                            "impactToken", freshToken)));
        }

        Map<String, Object> response = new LinkedHashMap<>();
        response.put("message", "Rule deleted successfully.");
        response.put("operation", "deleted");
        response.put("deletedRule", RuleToolPresenter.present(
                mutation.getAffectedItem(), safeList(boardStorageService.getNodes(userId))));
        response.put("totalRules", mutation.getCurrentCount());
        return successJson(response, "Rule deleted successfully.");
    }

    private String normalizeRelation(String relation) {
        String normalized = SmvRelationUtils.normalizeRelation(relation);
        if (normalized == null || normalized.isBlank()) {
            return null;
        }
        return SmvRelationUtils.isSupportedRelation(normalized) ? normalized : null;
    }

    private String normalizeTargetType(String targetType) {
        if (targetType == null) {
            return null;
        }
        String normalized = targetType.trim().toLowerCase(Locale.ROOT);
        if (normalized.isEmpty()) {
            return null;
        }
        return TARGET_TYPES.contains(normalized) ? normalized : null;
    }

    private Set<String> getDeviceIds(List<DeviceNodeDto> nodes) {
        Set<String> ids = new java.util.HashSet<>();
        for (DeviceNodeDto node : nodes) {
            String id = node != null ? trimToNull(node.getId()) : null;
            if (id != null) {
                ids.add(id);
            }
        }
        return ids;
    }

    private Map<String, String> labelsById(List<DeviceNodeDto> nodes) {
        Map<String, String> labels = new HashMap<>();
        for (DeviceNodeDto node : nodes) {
            String id = node != null ? trimToNull(node.getId()) : null;
            if (id == null) {
                continue;
            }
            String label = trimToNull(node.getLabel());
            labels.put(id, label != null ? label : id);
        }
        return labels;
    }

    private String buildRuleString(List<RuleDto.Condition> conditions,
                                   RuleDto.Command command,
                                   Map<String, String> labelsById) {
        List<String> conditionTexts = new ArrayList<>();
        for (RuleDto.Condition condition : conditions) {
            conditionTexts.add(describeCondition(condition, labelsById));
        }
        return "IF " + String.join(" AND ", conditionTexts)
                + " THEN " + describeCommand(command, labelsById);
    }

    private String describeCondition(RuleDto.Condition condition, Map<String, String> labelsById) {
        String device = displayName(condition.getDeviceName(), labelsById);
        String targetType = trimToNull(condition.getTargetType());
        String attribute = trimToNull(condition.getAttribute());
        if ("api".equals(targetType)) {
            return device + " emits " + attribute;
        }
        return device + "." + attribute + " " + condition.getRelation() + " " + condition.getValue();
    }

    private String describeCommand(RuleDto.Command command, Map<String, String> labelsById) {
        String text = displayName(command.getDeviceName(), labelsById) + "." + command.getAction();
        String contentDevice = trimToNull(command.getContentDevice());
        String content = trimToNull(command.getContent());
        if (contentDevice != null || content != null) {
            text += " with";
            if (content != null) {
                text += " content " + content;
            }
            if (contentDevice != null) {
                text += " from " + displayName(contentDevice, labelsById);
            }
        }
        return text;
    }

    private String displayName(String deviceId, Map<String, String> labelsById) {
        String id = trimToNull(deviceId);
        if (id == null) {
            return "unknown-device";
        }
        String label = labelsById.get(id);
        return label != null ? label : id;
    }

    private boolean isEmptyValueList(String value) {
        if (value == null) {
            return true;
        }
        for (String item : value.split("[,;|]")) {
            if (item != null && !item.trim().isEmpty()) {
                return false;
            }
        }
        return true;
    }
}
