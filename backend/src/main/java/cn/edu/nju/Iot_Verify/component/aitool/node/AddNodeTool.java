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
                return "{\"error\": \"User not logged in\"}";
            }

            JsonNode args = objectMapper.readTree(argsJson);
            String templateName = args.path("templateName").asText();
            String label = args.has("label") ? args.path("label").asText() : null;
            Double x = args.has("x") ? args.path("x").asDouble() : null;
            Double y = args.has("y") ? args.path("y").asDouble() : null;
            Integer w = args.has("w") ? args.path("w").asInt() : null;
            Integer h = args.has("h") ? args.path("h").asInt() : null;
            String state = args.has("state") ? args.path("state").asText() : null;

            log.info("Executing add_device: {}", label);

            return nodeService.addNode(userId, templateName, label, x, y, state, w, h);

        } catch (Exception e) {
            log.error("add_device failed", e);
            return "{\"error\": \"Add failed: " + e.getMessage() + "\"}";
        }
    }
}
