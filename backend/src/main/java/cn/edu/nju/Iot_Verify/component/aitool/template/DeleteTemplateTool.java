package cn.edu.nju.Iot_Verify.component.aitool.template;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
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

import java.util.HashMap;
import java.util.List;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class DeleteTemplateTool implements AiTool {

    private final BoardStorageService boardStorageService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "delete_template";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("templateId", Map.of(
                "type", "string",
                "description", "The ID of the template to delete (from list_templates result)."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, List.of("templateId")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Delete a device template. Use list_templates first to find the template ID.")
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

            JsonNode args = objectMapper.readTree(argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
            String templateId = trimToNull(args.path("templateId").asText(null));
            if (templateId == null) {
                return "{\"error\": \"Template ID is required.\"}";
            }

            boardStorageService.deleteDeviceTemplate(userId, templateId);
            return "{\"message\": \"Template deleted successfully.\"}";
        } catch (Exception e) {
            log.error("delete_template failed", e);
            return "{\"error\": \"Failed to delete template: " + e.getMessage() + "\"}";
        }
    }

    private String trimToNull(String value) {
        if (value == null) {
            return null;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }
}
