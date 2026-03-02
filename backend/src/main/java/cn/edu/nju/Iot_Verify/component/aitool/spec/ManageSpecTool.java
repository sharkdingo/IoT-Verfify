package cn.edu.nju.Iot_Verify.component.aitool.spec;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.UUID;

@Slf4j
@Component
@RequiredArgsConstructor
public class ManageSpecTool implements AiTool {

    private static final Set<String> TARGET_TYPES = Set.of("state", "variable", "api", "trust", "privacy");
    private static final Set<String> RELATIONS = Set.of("=", "!=", ">", "<", ">=", "<=", "in", "not in");
    private static final Set<String> API_STATE_RELATIONS = Set.of("=", "!=", "in", "not in");
    private static final Set<String> TEMPLATE_IDS = Set.of("1", "2", "3", "4", "5", "6", "7");

    private final BoardStorageService boardStorageService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "manage_spec";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> conditionItemSchema = Map.of(
                "type", "object",
                "properties", Map.of(
                        "deviceId", Map.of("type", "string", "description", "Device node ID on the board"),
                        "deviceLabel", Map.of("type", "string", "description", "Device display name"),
                        "targetType", Map.of("type", "string", "enum", List.of("state", "variable", "api", "trust", "privacy"),
                                "description", "What to check: state, variable, api signal, trust level, or privacy level"),
                        "key", Map.of("type", "string", "description", "The key to check (e.g. state, variable name, API name)"),
                        "relation", Map.of("type", "string", "description", "Comparison: =, !=, >, <, >=, <=, in, not in"),
                        "value", Map.of("type", "string", "description", "Expected value")
                ),
                "required", List.of("deviceId", "targetType", "key")
        );

        Map<String, Object> props = new HashMap<>();
        props.put("action", Map.of(
                "type", "string",
                "enum", List.of("add", "delete"),
                "description", "Action to perform: add to create a new specification, delete to remove one."
        ));
        props.put("templateId", Map.of(
                "type", "string",
                "description", "Optional for add. A short ID for the spec template (e.g. 1,2,3,4,5,6,7)."
        ));
        props.put("templateLabel", Map.of(
                "type", "string",
                "description", "Optional for add. Human-readable label for the property."
        ));
        props.put("aConditions", Map.of(
                "type", "array",
                "description", "For add. A-part conditions. Can be empty.",
                "items", conditionItemSchema
        ));
        props.put("ifConditions", Map.of(
                "type", "array",
                "description", "For add. IF-part conditions. Can be empty.",
                "items", conditionItemSchema
        ));
        props.put("thenConditions", Map.of(
                "type", "array",
                "description", "For add. THEN-part conditions. Optional for A-only templates and required for implication-style templates.",
                "items", conditionItemSchema
        ));
        props.put("specId", Map.of(
                "type", "string",
                "description", "Required for delete. The ID of the specification to delete."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema("object", props, List.of("action"));

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Add or delete a formal specification. Use list_specs to inspect existing specs before deleting.")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    public String execute(String argsJson) {
        try {
            Long userId = UserContextHolder.getUserId();
            if (userId == null) {
                return errorJson("User not logged in");
            }

            JsonNode args = objectMapper.readTree(argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
            String action = args.path("action").asText("").trim().toLowerCase(Locale.ROOT);

            return switch (action) {
                case "add" -> executeAdd(userId, args);
                case "delete" -> executeDelete(userId, args);
                default -> errorJson("Unknown action: " + action + ". Use 'add' or 'delete'.");
            };
        } catch (Exception e) {
            log.error("manage_spec failed", e);
            return errorJson("Spec operation failed. Please check parameters and retry.");
        }
    }

    private String executeAdd(Long userId, JsonNode args) throws Exception {
        List<SpecConditionDto> aConditions = parseConditions(args.path("aConditions"), "a");
        List<SpecConditionDto> ifConditions = parseConditions(args.path("ifConditions"), "if");
        List<SpecConditionDto> thenConditions = parseConditions(args.path("thenConditions"), "then");

        if (aConditions.isEmpty() && ifConditions.isEmpty() && thenConditions.isEmpty()) {
            return errorJson("At least one valid condition is required in 'aConditions', 'ifConditions', or 'thenConditions'.");
        }

        String templateId = trimToNull(args.path("templateId").asText(null));
        if (templateId == null) {
            templateId = "1";
        }
        if (!TEMPLATE_IDS.contains(templateId)) {
            return errorJson("Unsupported templateId '" + templateId + "'. Allowed: 1,2,3,4,5,6,7.");
        }
        String templateLabel = trimToNull(args.path("templateLabel").asText(null));
        if (templateLabel == null) {
            templateLabel = "Spec " + templateId;
        }

        String templateCheckError = validateTemplateShape(templateId, aConditions, ifConditions, thenConditions);
        if (templateCheckError != null) {
            return errorJson(templateCheckError);
        }

        SpecificationDto spec = new SpecificationDto();
        spec.setId(UUID.randomUUID().toString());
        spec.setTemplateId(templateId);
        spec.setTemplateLabel(templateLabel);
        spec.setAConditions(aConditions);
        spec.setIfConditions(ifConditions);
        spec.setThenConditions(thenConditions);

        List<SpecificationDto> existing = new ArrayList<>(safeList(boardStorageService.getSpecs(userId)));
        existing.add(spec);
        List<SpecificationDto> saved = boardStorageService.saveSpecs(userId, existing);

        return objectMapper.writeValueAsString(Map.of(
                "message", "Specification added successfully.",
                "specId", spec.getId(),
                "totalSpecs", saved.size()
        ));
    }

    private String executeDelete(Long userId, JsonNode args) throws Exception {
        String specId = trimToNull(args.path("specId").asText(null));
        if (specId == null) {
            return errorJson("'specId' is required for delete action.");
        }

        List<SpecificationDto> existing = new ArrayList<>(safeList(boardStorageService.getSpecs(userId)));
        boolean removed = existing.removeIf(s -> specId.equals(s.getId()));
        if (!removed) {
            return errorJson("Specification with ID '" + specId + "' not found.");
        }

        List<SpecificationDto> saved = boardStorageService.saveSpecs(userId, existing);
        return objectMapper.writeValueAsString(Map.of(
                "message", "Specification deleted successfully.",
                "totalSpecs", saved.size()
        ));
    }

    private List<SpecConditionDto> parseConditions(JsonNode node, String side) {
        List<SpecConditionDto> conditions = new ArrayList<>();
        if (node == null || node.isMissingNode() || !node.isArray()) {
            return conditions;
        }

        int index = 0;
        for (JsonNode cn : node) {
            String deviceId = trimToNull(cn.path("deviceId").asText(null));
            String targetType = trimToNull(cn.path("targetType").asText(null));
            String key = trimToNull(cn.path("key").asText(null));

            if (deviceId == null || targetType == null || key == null) {
                throw new IllegalArgumentException("Condition index " + index + " on '" + side
                        + "' must include non-empty deviceId, targetType, and key.");
            }

            String normalizedTargetType = targetType.toLowerCase(Locale.ROOT);
            if (!TARGET_TYPES.contains(normalizedTargetType)) {
                throw new IllegalArgumentException("Condition index " + index + " on '" + side
                        + "' has unsupported targetType '" + targetType
                        + "'. Allowed: state, variable, api, trust, privacy.");
            }

            String relationInput = trimToNull(cn.path("relation").asText(null));
            String relation = normalizeRelation(relationInput);
            String value = trimToNull(cn.path("value").asText(null));

            if (relationInput != null && relation == null) {
                throw new IllegalArgumentException("Condition index " + index + " on '" + side
                        + "' has unsupported relation '" + relationInput
                        + "'. Allowed: =, !=, >, <, >=, <=, in, not in.");
            }

            if (relation == null && value != null) {
                relation = "=";
            }
            if ("api".equals(normalizedTargetType)) {
                if (relation == null) {
                    relation = "=";
                }
                if (value == null) {
                    value = "TRUE";
                }
            }

            if (relation == null || value == null) {
                throw new IllegalArgumentException("Condition index " + index + " on '" + side
                        + "' requires relation/value (api allows default '= TRUE').");
            }

            if (("in".equals(relation) || "not in".equals(relation)) && isEmptyValueList(value)) {
                throw new IllegalArgumentException("Condition index " + index + " on '" + side
                        + "' has empty value list for relation '" + relation + "'.");
            }

            if (("state".equals(normalizedTargetType) || "api".equals(normalizedTargetType))
                    && !API_STATE_RELATIONS.contains(relation)) {
                throw new IllegalArgumentException("Condition index " + index + " on '" + side
                        + "' targetType='" + normalizedTargetType + "' only supports =, !=, in, not in.");
            }

            SpecConditionDto dto = new SpecConditionDto();
            dto.setId(UUID.randomUUID().toString());
            dto.setSide(side);
            dto.setDeviceId(deviceId);
            String deviceLabel = trimToNull(cn.path("deviceLabel").asText(null));
            dto.setDeviceLabel(deviceLabel != null ? deviceLabel : deviceId);
            dto.setTargetType(normalizedTargetType);
            dto.setKey(key);
            dto.setRelation(relation);
            dto.setValue(value);
            conditions.add(dto);
            index++;
        }
        return conditions;
    }

    private String validateTemplateShape(String templateId,
                                         List<SpecConditionDto> aConditions,
                                         List<SpecConditionDto> ifConditions,
                                         List<SpecConditionDto> thenConditions) {
        // template 2/3/7 use aConditions only
        if ("2".equals(templateId) || "3".equals(templateId) || "7".equals(templateId)) {
            if (aConditions.isEmpty()) {
                return "Template " + templateId + " requires non-empty aConditions.";
            }
            return null;
        }

        // implication templates require both if and then
        if ("4".equals(templateId) || "5".equals(templateId) || "6".equals(templateId)) {
            if (ifConditions.isEmpty() || thenConditions.isEmpty()) {
                return "Template " + templateId + " requires non-empty ifConditions and thenConditions.";
            }
            return null;
        }

        // template 1: allow either A-only or IF-THEN
        if ("1".equals(templateId)) {
            boolean validA = !aConditions.isEmpty();
            boolean validImplication = !ifConditions.isEmpty() && !thenConditions.isEmpty();
            if (!validA && !validImplication) {
                return "Template 1 requires non-empty aConditions, or both ifConditions and thenConditions.";
            }
        }
        return null;
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
        return RELATIONS.contains(normalized) ? normalized : null;
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

    private String trimToNull(String value) {
        if (value == null) {
            return null;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }

    private <T> List<T> safeList(List<T> list) {
        return list == null ? List.of() : list;
    }

    private String errorJson(String message) {
        try {
            return objectMapper.writeValueAsString(Map.of("error", message));
        } catch (Exception e) {
            Map<String, Object> fallback = new LinkedHashMap<>();
            fallback.put("error", message);
            return fallback.toString();
        }
    }
}
