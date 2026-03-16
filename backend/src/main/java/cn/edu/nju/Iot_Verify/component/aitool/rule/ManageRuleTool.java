package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;

@Slf4j
@Component
public class ManageRuleTool extends AbstractAiTool {

    private static final Set<String> ALLOWED_RELATIONS = Set.of(
            "=", "!=", ">", "<", ">=", "<=", "in", "not in"
    );

    private final BoardStorageService boardStorageService;

    public ManageRuleTool(BoardStorageService boardStorageService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardStorageService = boardStorageService;
    }

    @Override
    public String getName() {
        return "manage_rule";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("action", Map.of(
                "type", "string",
                "enum", List.of("add", "delete"),
                "description", "Action to perform: 'add' to create a new rule, 'delete' to remove an existing rule."
        ));

        props.put("conditions", Map.of(
                "type", "array",
                "description", "Required for 'add'. Each condition: {deviceName, attribute, relation, value}. relation supports =, !=, >, <, >=, <=, in, not in.",
                "items", Map.of(
                        "type", "object",
                        "properties", Map.of(
                                "deviceName", Map.of("type", "string"),
                                "attribute", Map.of("type", "string"),
                                "relation", Map.of("type", "string"),
                                "value", Map.of("type", "string")
                        ),
                        "required", List.of("deviceName", "attribute")
                )
        ));

        props.put("command", Map.of(
                "type", "object",
                "description", "Required for 'add'. The action to execute when conditions are met.",
                "properties", Map.of(
                        "deviceName", Map.of("type", "string"),
                        "action", Map.of("type", "string"),
                        "contentDevice", Map.of("type", "string"),
                        "content", Map.of("type", "string")
                ),
                "required", List.of("deviceName", "action")
        ));

        props.put("ruleId", Map.of(
                "type", "integer",
                "description", "Required for 'delete'. The ID of the rule to delete (from list_rules result)."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, List.of("action")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Add or delete an automation rule. Use list_rules first to see existing rules before deleting.")
                        .parameters(schema)
                        .build()
        );
    }

    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }
            String action = args.path("action").asText("").trim().toLowerCase(Locale.ROOT);

            return switch (action) {
                case "add" -> executeAdd(userId, args);
                case "delete" -> executeDelete(userId, args);
                default -> errorJson("Unknown action: " + action + ". Use 'add' or 'delete'.",
                        "VALIDATION_ERROR", 400);
            };
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
        JsonNode conditionsNode = args.path("conditions");
        JsonNode commandNode = args.path("command");

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
            String deviceName = trimToNull(cn.path("deviceName").asText(null));
            String attribute = trimToNull(cn.path("attribute").asText(null));
            if (deviceName == null || attribute == null) {
                return errorJson("Each condition must include non-empty 'deviceName' and 'attribute'. Invalid condition index: " + index,
                        "VALIDATION_ERROR", 400);
            }

            String relationInput = trimToNull(cn.path("relation").asText(null));
            String relation = normalizeRelation(relationInput);
            String value = trimToNull(cn.path("value").asText(null));

            if (relationInput != null && relation == null) {
                return errorJson("Unsupported relation '" + relationInput + "' at condition index " + index
                        + ". Allowed: =, !=, >, <, >=, <=, in, not in.",
                        "VALIDATION_ERROR", 400);
            }

            // Friendly fallback for API-signal shorthand.
            if (relation == null && value == null) {
                relation = null;
            } else if (relation == null) {
                relation = "=";
            }

            if (relation != null && value == null) {
                if ("=".equals(relation) || "!=".equals(relation)) {
                    value = "TRUE";
                } else {
                    return errorJson("Condition value is required when relation is '" + relation
                            + "'. Invalid condition index: " + index,
                            "VALIDATION_ERROR", 400);
                }
            }

            if (("in".equals(relation) || "not in".equals(relation)) && isEmptyValueList(value)) {
                return errorJson("Condition value list cannot be empty for relation '" + relation
                        + "'. Invalid condition index: " + index,
                        "VALIDATION_ERROR", 400);
            }

            conditions.add(RuleDto.Condition.builder()
                    .deviceName(deviceName)
                    .attribute(attribute)
                    .relation(relation)
                    .value(value)
                    .build());
            index++;
        }

        String commandDeviceName = trimToNull(commandNode.path("deviceName").asText(null));
        String commandAction = trimToNull(commandNode.path("action").asText(null));
        if (commandDeviceName == null || commandAction == null) {
            return errorJson("Command must include non-empty 'deviceName' and 'action'.",
                    "VALIDATION_ERROR", 400);
        }

        RuleDto.Command command = RuleDto.Command.builder()
                .deviceName(commandDeviceName)
                .action(commandAction)
                .contentDevice(trimToNull(commandNode.path("contentDevice").asText(null)))
                .content(trimToNull(commandNode.path("content").asText(null)))
                .build();

        RuleDto newRule = RuleDto.builder()
                .userId(userId)
                .conditions(conditions)
                .command(command)
                .build();

        List<RuleDto> saved = boardStorageService.addRule(userId, newRule);

        return successJson(Map.of(
                "message", "Rule added successfully.",
                "totalRules", saved.size()
        ), "Rule added successfully.");
    }

    private String executeDelete(Long userId, JsonNode args) throws Exception {
        if (!args.has("ruleId") || !args.path("ruleId").canConvertToLong()) {
            return errorJson("'ruleId' is required for delete action.",
                    "VALIDATION_ERROR", 400);
        }
        long ruleId = args.path("ruleId").asLong();
        if (ruleId <= 0) {
            return errorJson("'ruleId' must be a positive integer.",
                    "VALIDATION_ERROR", 400);
        }

        List<RuleDto> remaining = boardStorageService.removeRule(userId, ruleId);

        if (remaining == null) {
            return errorJson("Rule with ID " + ruleId + " not found.",
                    "NOT_FOUND", 404);
        }

        return successJson(Map.of(
                "message", "Rule deleted successfully.",
                "totalRules", remaining.size()
        ), "Rule deleted successfully.");
    }

    private String normalizeRelation(String relation) {
        if (relation == null) {
            return null;
        }
        String normalized = relation.trim();
        if (normalized.isEmpty()) {
            return null;
        }
        normalized = switch (normalized.toUpperCase(Locale.ROOT)) {
            case "EQ", "==" -> "=";
            case "NEQ", "!=" -> "!=";
            case "GT" -> ">";
            case "GTE" -> ">=";
            case "LT" -> "<";
            case "LTE" -> "<=";
            case "IN" -> "in";
            case "NOT_IN", "NOT IN" -> "not in";
            default -> normalized;
        };
        return ALLOWED_RELATIONS.contains(normalized) ? normalized : null;
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
