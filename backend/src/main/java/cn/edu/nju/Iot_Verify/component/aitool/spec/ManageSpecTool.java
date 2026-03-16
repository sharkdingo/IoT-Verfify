package cn.edu.nju.Iot_Verify.component.aitool.spec;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
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
import java.util.UUID;

@Slf4j
@Component
public class ManageSpecTool extends AbstractAiTool {

    private static final Set<String> TARGET_TYPES = Set.of("state", "variable", "api", "trust", "privacy");
    private static final Set<String> RELATIONS = Set.of("=", "!=", ">", "<", ">=", "<=", "in", "not in");
    private static final Set<String> API_STATE_RELATIONS = Set.of("=", "!=", "in", "not in");
    private static final Set<String> TEMPLATE_IDS = Set.of("1", "2", "3", "4", "5", "6", "7");

    private final BoardStorageService boardStorageService;

    public ManageSpecTool(BoardStorageService boardStorageService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardStorageService = boardStorageService;
    }

    @Override
    public String getName() {
        return "manage_spec";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> conditionItemSchema = Map.of(
                "type", "object",
                "properties", Map.of(
                        "deviceId", Map.of("type", "string", "description", "Device node ID on the board (optional when deviceLabel is provided)"),
                        "deviceLabel", Map.of("type", "string", "description", "Device display name (optional when deviceId is provided)"),
                        "targetType", Map.of("type", "string", "enum", List.of("state", "variable", "api", "trust", "privacy"),
                                "description", "What to check: state, variable, api signal, trust level, or privacy level"),
                        "key", Map.of("type", "string", "description", "The key to check (e.g. state, variable name, API name)"),
                        "relation", Map.of("type", "string", "description", "Comparison: =, !=, >, <, >=, <=, in, not in"),
                        "value", Map.of("type", "string", "description", "Expected value")
                ),
                "required", List.of("targetType", "key")
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
        } catch (IllegalArgumentException e) {
            log.warn("manage_spec validation failed: {}", e.getMessage());
            return errorJson(e.getMessage(), "VALIDATION_ERROR", 400);
        } catch (ServiceUnavailableException e) {
            log.warn("manage_spec busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("manage_spec business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("manage_spec failed", e);
            return errorJson("Spec operation failed. Please check parameters and retry.",
                    "INTERNAL_ERROR", 500);
        }
    }

    private String executeAdd(Long userId, JsonNode args) throws Exception {
        DeviceLookup deviceLookup = buildDeviceLookup(userId);
        List<SpecConditionDto> aConditions = parseConditions(args.path("aConditions"), "a", deviceLookup);
        List<SpecConditionDto> ifConditions = parseConditions(args.path("ifConditions"), "if", deviceLookup);
        List<SpecConditionDto> thenConditions = parseConditions(args.path("thenConditions"), "then", deviceLookup);

        if (aConditions.isEmpty() && ifConditions.isEmpty() && thenConditions.isEmpty()) {
            return errorJson("At least one valid condition is required in 'aConditions', 'ifConditions', or 'thenConditions'.",
                    "VALIDATION_ERROR", 400);
        }

        String templateId = trimToNull(args.path("templateId").asText(null));
        if (templateId == null) {
            templateId = "1";
        }
        if (!TEMPLATE_IDS.contains(templateId)) {
            return errorJson("Unsupported templateId '" + templateId + "'. Allowed: 1,2,3,4,5,6,7.",
                    "VALIDATION_ERROR", 400);
        }
        String templateLabel = trimToNull(args.path("templateLabel").asText(null));
        if (templateLabel == null) {
            templateLabel = "Spec " + templateId;
        }

        String templateCheckError = validateTemplateShape(templateId, aConditions, ifConditions, thenConditions);
        if (templateCheckError != null) {
            return errorJson(templateCheckError, "VALIDATION_ERROR", 400);
        }

        SpecificationDto spec = new SpecificationDto();
        spec.setId(UUID.randomUUID().toString());
        spec.setTemplateId(templateId);
        spec.setTemplateLabel(templateLabel);
        spec.setAConditions(aConditions);
        spec.setIfConditions(ifConditions);
        spec.setThenConditions(thenConditions);

        List<SpecificationDto> saved = boardStorageService.addSpec(userId, spec);

        return successJson(Map.of(
                "message", "Specification added successfully.",
                "specId", spec.getId(),
                "totalSpecs", saved.size()
        ), "Specification added successfully.");
    }

    private String executeDelete(Long userId, JsonNode args) throws Exception {
        String specId = trimToNull(args.path("specId").asText(null));
        if (specId == null) {
            return errorJson("'specId' is required for delete action.",
                    "VALIDATION_ERROR", 400);
        }

        List<SpecificationDto> remaining = boardStorageService.removeSpec(userId, specId);
        if (remaining == null) {
            return errorJson("Specification with ID '" + specId + "' not found.",
                    "NOT_FOUND", 404);
        }

        return successJson(Map.of(
                "message", "Specification deleted successfully.",
                "totalSpecs", remaining.size()
        ), "Specification deleted successfully.");
    }

    private List<SpecConditionDto> parseConditions(JsonNode node, String side, DeviceLookup deviceLookup) {
        List<SpecConditionDto> conditions = new ArrayList<>();
        if (node == null || node.isMissingNode() || !node.isArray()) {
            return conditions;
        }

        int index = 0;
        for (JsonNode cn : node) {
            String inputDeviceId = trimToNull(cn.path("deviceId").asText(null));
            String inputDeviceLabel = trimToNull(cn.path("deviceLabel").asText(null));
            String resolvedById = null;
            String resolvedByLabel = null;

            if (inputDeviceId != null) {
                resolvedById = resolveDeviceIdById(inputDeviceId, deviceLookup);
                if (resolvedById == null) {
                    throw new IllegalArgumentException("Condition index " + index + " on '" + side
                            + "' cannot resolve deviceId '" + inputDeviceId + "' to an existing device.");
                }
            }

            if (inputDeviceLabel != null) {
                List<String> matchedIds = resolveDeviceIdsByLabel(inputDeviceLabel, deviceLookup);
                if (matchedIds.isEmpty()) {
                    throw new IllegalArgumentException("Condition index " + index + " on '" + side
                            + "' cannot resolve deviceLabel '" + inputDeviceLabel + "' to an existing deviceId.");
                }
                if (matchedIds.size() > 1) {
                    throw new IllegalArgumentException("Condition index " + index + " on '" + side
                            + "' has ambiguous deviceLabel '" + inputDeviceLabel
                            + "', matched deviceIds: " + matchedIds + ".");
                }
                resolvedByLabel = matchedIds.get(0);
            }

            String deviceId = resolvedById != null ? resolvedById : resolvedByLabel;
            if (resolvedById != null && resolvedByLabel != null && !resolvedById.equals(resolvedByLabel)) {
                throw new IllegalArgumentException("Condition index " + index + " on '" + side
                        + "' has inconsistent deviceId/deviceLabel: deviceId '" + inputDeviceId
                        + "' maps to '" + resolvedById + "', but deviceLabel '" + inputDeviceLabel
                        + "' maps to '" + resolvedByLabel + "'.");
            }
            String targetType = trimToNull(cn.path("targetType").asText(null));
            String key = trimToNull(cn.path("key").asText(null));

            if (deviceId == null || targetType == null || key == null) {
                throw new IllegalArgumentException("Condition index " + index + " on '" + side
                        + "' must include non-empty targetType/key, and either deviceId or resolvable deviceLabel.");
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
            dto.setDeviceLabel(inputDeviceLabel != null ? inputDeviceLabel : deviceId);
            dto.setTargetType(normalizedTargetType);
            dto.setKey(key);
            dto.setRelation(relation);
            dto.setValue(value);
            conditions.add(dto);
            index++;
        }
        return conditions;
    }

    private DeviceLookup buildDeviceLookup(Long userId) {
        Map<String, String> idsByKey = new HashMap<>();
        Map<String, List<String>> idsByLabelKey = new HashMap<>();
        for (DeviceNodeDto node : safeList(boardStorageService.getNodes(userId))) {
            if (node == null) {
                continue;
            }
            String id = trimToNull(node.getId());
            if (id == null) {
                continue;
            }
            idsByKey.put(normalizeLookupKey(id), id);
            String label = trimToNull(node.getLabel());
            if (label != null) {
                String labelKey = normalizeLookupKey(label);
                List<String> ids = idsByLabelKey.computeIfAbsent(labelKey, k -> new ArrayList<>());
                if (!ids.contains(id)) {
                    ids.add(id);
                }
            }
        }
        return new DeviceLookup(idsByKey, idsByLabelKey);
    }

    private String resolveDeviceIdById(String value, DeviceLookup lookup) {
        if (value == null || lookup == null || lookup.idsByKey().isEmpty()) {
            return null;
        }
        return lookup.idsByKey().get(normalizeLookupKey(value));
    }

    private List<String> resolveDeviceIdsByLabel(String value, DeviceLookup lookup) {
        if (value == null || lookup == null || lookup.idsByLabelKey().isEmpty()) {
            return List.of();
        }
        List<String> ids = lookup.idsByLabelKey().get(normalizeLookupKey(value));
        return ids == null ? List.of() : ids;
    }

    private String normalizeLookupKey(String value) {
        return value.trim().toLowerCase(Locale.ROOT);
    }

    private record DeviceLookup(Map<String, String> idsByKey, Map<String, List<String>> idsByLabelKey) {
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
                return "Template 1 (always): requires non-empty aConditions for AG(A), or both ifConditions and thenConditions for AG(IF→THEN).";
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
}
