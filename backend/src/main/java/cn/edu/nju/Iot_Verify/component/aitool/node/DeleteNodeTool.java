package cn.edu.nju.Iot_Verify.component.aitool.node;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.NodeService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class DeleteNodeTool implements AiTool {

    private final NodeService nodeService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "delete_device";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("label", Map.of("type", "string", "description", "Device name (label)"));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.singletonList("label")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Delete a device node")
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
            String label = args.path("label").asText();
            if (label == null || label.isEmpty()) return "{\"error\": \"Missing label\"}";

            log.info("Executing delete_device, label: {}", label);
            return nodeService.deleteNode(userId, label);
        } catch (Exception e) {
            log.error("delete_device failed", e);
            return "{\"error\": \"Delete failed: " + e.getMessage() + "\"}";
        }
    }
}
