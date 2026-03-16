package cn.edu.nju.Iot_Verify.component.aitool.node;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.NodeService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.HashMap;
import java.util.List;
import java.util.LinkedHashMap;
import java.util.Map;

@Slf4j
@Component
public class AddNodeTool extends AbstractAiTool {

    private final NodeService nodeService;

    public AddNodeTool(NodeService nodeService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.nodeService = nodeService;
    }

    @Override
    public String getName() {
        return "add_device";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();

        String templateDesc = "Device template type name. Use board_overview tool to see available templates. " +
                "Map user aliases to standard names. Do not modify template names like Air Purifier to Air_Purifier. " +
                "If device is semantically unrelated to all templates, pass original name.";
        props.put("templateName", Map.of("type", "string", "description", templateDesc));

        String labelDesc = "Device display name (ID). Only fill if user explicitly specifies a name. " +
                "If user just says 'create an AC' without naming it, pass null. Do not invent names!";
        props.put("label", Map.of("type", "string", "description", labelDesc));

        props.put("x", Map.of("type", "number", "description", "X coordinate (default 250)"));
        props.put("y", Map.of("type", "number", "description", "Y coordinate (default 250)"));
        props.put("w", Map.of("type", "integer", "description", "Width (default 110)"));
        props.put("h", Map.of("type", "integer", "description", "Height (default 90)"));
        props.put("state", Map.of("type", "string", "description", "Initial state. Leave null to use template default."));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, List.of("templateName")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Add a new device")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }
            String templateName = args.path("templateName").asText("").trim();
            if (templateName.isEmpty()) {
                return errorJson("Template name is required.", "VALIDATION_ERROR", 400);
            }

            String label = args.has("label") ? trimToNull(args.path("label").asText(null)) : null;
            Double x = parseDoubleOrNull(args, "x");
            Double y = parseDoubleOrNull(args, "y");
            Integer w = parseIntOrNull(args, "w");
            Integer h = parseIntOrNull(args, "h");
            String state = args.has("state") ? trimToNull(args.path("state").asText(null)) : null;

            log.info("Executing add_device: {}", label);

            String raw = nodeService.addNode(userId, templateName, label, x, y, state, w, h);
            return normalizeResult(raw);

        } catch (ServiceUnavailableException e) {
            log.warn("add_device busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("add_device business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("add_device failed", e);
            return errorJson("Add device failed. Please retry.", "INTERNAL_ERROR", 500);
        }
    }

    private Double parseDoubleOrNull(JsonNode args, String field) {
        if (!args.has(field)) return null;
        JsonNode node = args.path(field);
        if (node.isNull() || (!node.isNumber() && node.asText("").isEmpty())) return null;
        if (node.isNumber()) return node.asDouble();
        try {
            return Double.parseDouble(node.asText());
        } catch (NumberFormatException e) {
            return null;
        }
    }

    private Integer parseIntOrNull(JsonNode args, String field) {
        if (!args.has(field)) return null;
        JsonNode node = args.path(field);
        if (node.isNull() || (!node.isNumber() && node.asText("").isEmpty())) return null;
        if (node.isNumber()) return node.asInt();
        try {
            return Integer.parseInt(node.asText());
        } catch (NumberFormatException e) {
            return null;
        }
    }

    private String normalizeResult(String raw) {
        if (raw == null || raw.isBlank()) {
            return AiToolResponseHelper.success(objectMapper, "Device operation completed.");
        }

        try {
            JsonNode root = objectMapper.readTree(raw);
            if (root.isObject()) {
                return raw;
            }
        } catch (Exception ignore) {
        }

        Map<String, Object> body = new LinkedHashMap<>();
        body.put("message", raw);
        return AiToolResponseHelper.success(objectMapper, body, raw);
    }
}
