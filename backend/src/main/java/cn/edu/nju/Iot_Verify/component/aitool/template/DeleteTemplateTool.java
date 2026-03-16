package cn.edu.nju.Iot_Verify.component.aitool.template;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
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

import java.util.HashMap;
import java.util.List;
import java.util.Map;

@Slf4j
@Component
public class DeleteTemplateTool extends AbstractAiTool {

    private final BoardStorageService boardStorageService;

    public DeleteTemplateTool(BoardStorageService boardStorageService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardStorageService = boardStorageService;
    }

    @Override
    public String getName() {
        return "delete_template";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("templateId", Map.of(
                "type", "integer",
                "description", "The numeric ID of the template to delete (from list_templates result)."
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

    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }
            JsonNode templateIdNode = args.path("templateId");
            if (templateIdNode.isMissingNode() || templateIdNode.isNull()) {
                return errorJson("Template ID is required.", "VALIDATION_ERROR", 400);
            }
            long templateId;
            if (templateIdNode.isIntegralNumber()) {
                if (!templateIdNode.canConvertToLong()) {
                    return errorJson("Template ID is out of range.", "VALIDATION_ERROR", 400);
                }
                templateId = templateIdNode.asLong();
            } else {
                // Fallback: try parsing string representation
                String raw = trimToNull(templateIdNode.asText(null));
                if (raw == null) {
                    return errorJson("Template ID is required.", "VALIDATION_ERROR", 400);
                }
                try {
                    templateId = Long.parseLong(raw.trim());
                } catch (NumberFormatException e) {
                    return errorJson("Template ID must be a number.", "VALIDATION_ERROR", 400);
                }
            }

            boardStorageService.deleteDeviceTemplate(userId, templateId);
            return successJson(Map.of("message", "Template deleted successfully."), "Template deleted successfully.");
        } catch (ServiceUnavailableException e) {
            log.warn("delete_template busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("delete_template business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("delete_template failed", e);
            return errorJson("Failed to delete template.", "INTERNAL_ERROR", 500);
        }
    }
}
