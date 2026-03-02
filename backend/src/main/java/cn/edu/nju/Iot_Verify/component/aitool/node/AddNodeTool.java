package cn.edu.nju.Iot_Verify.component.aitool.node;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.service.NodeService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.HashMap;
import java.util.List;
import java.util.LinkedHashMap;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class AddNodeTool implements AiTool {

    private final NodeService nodeService;
    private final ObjectMapper objectMapper;
    private final DeviceTemplateService deviceTemplateService;

    @Override
    public String getName() {
        return "add_device";
    }

    @Override
    public ChatTool getDefinition() {
        Long userId = UserContextHolder.getUserId();
        List<String> validTemplates = userId != null
                ? deviceTemplateService.getAllTemplateNames(userId)
                : List.of();
        String templateListStr = String.join(", ", validTemplates);

        Map<String, Object> props = new HashMap<>();

        String templateDesc = "Device template type name. System only supports: [" + templateListStr + "]. " +
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
    public String execute(String argsJson) {
        try {
            Long userId = UserContextHolder.getUserId();
            if (userId == null) {
                return errorJson("User not logged in");
            }

            JsonNode args = objectMapper.readTree(argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
            String templateName = args.path("templateName").asText("").trim();
            if (templateName.isEmpty()) {
                return errorJson("Template name is required.");
            }

            String label = args.has("label") ? trimToNull(args.path("label").asText(null)) : null;
            Double x = args.has("x") ? args.path("x").asDouble() : null;
            Double y = args.has("y") ? args.path("y").asDouble() : null;
            Integer w = args.has("w") ? args.path("w").asInt() : null;
            Integer h = args.has("h") ? args.path("h").asInt() : null;
            String state = args.has("state") ? trimToNull(args.path("state").asText(null)) : null;

            log.info("Executing add_device: {}", label);

            String raw = nodeService.addNode(userId, templateName, label, x, y, state, w, h);
            return normalizeResult(raw);

        } catch (Exception e) {
            log.error("add_device failed", e);
            return errorJson("Add device failed. Please retry.");
        }
    }

    private String trimToNull(String value) {
        if (value == null) {
            return null;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }

    private String normalizeResult(String raw) throws Exception {
        if (raw == null || raw.isBlank()) {
            return objectMapper.writeValueAsString(Map.of("message", "Device operation completed."));
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
        return objectMapper.writeValueAsString(body);
    }

    private String errorJson(String message) {
        try {
            return objectMapper.writeValueAsString(Map.of("error", message));
        } catch (Exception ex) {
            return "{\"error\":\"" + message + "\"}";
        }
    }
}
