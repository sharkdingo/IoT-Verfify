package cn.edu.nju.Iot_Verify.component.aitool.template;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.MapperFeature;
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
public class AddTemplateTool implements AiTool {

    private final BoardStorageService boardStorageService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "add_template";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("name", Map.of(
                "type", "string",
                "description", "Template name (e.g. 'Smart Lock', 'Temperature Sensor')"
        ));

        props.put("manifest", Map.of(
                "type", "object",
                "description", "Full device manifest JSON defining the device behavior. Must include: " +
                        "Name, Description, Modes (array of state names), InitState, " +
                        "WorkingStates (array of {Name, Description}), " +
                        "Transitions (array of {From, To, Trigger, Conditions[], Assignments[]}), " +
                        "APIs (array of {Name, Description, Trigger}). " +
                        "Optional: InternalVariables, ImpactedVariables, Contents."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, List.of("name", "manifest")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Add a custom device template. Templates define device behavior including states, transitions, and APIs. " +
                                "Use list_templates to see existing templates for reference.")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    public String execute(String argsJson) {
        try {
            Long userId = UserContextHolder.getUserId();
            if (userId == null) {
                return errorJson("User not logged in", "UNAUTHORIZED", 401);
            }

            JsonNode args;
            try {
                args = objectMapper.readTree(argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
            } catch (Exception parseEx) {
                return errorJson("Invalid JSON arguments.", "VALIDATION_ERROR", 400);
            }
            String name = trimToNull(args.path("name").asText(null));
            if (name == null) {
                return errorJson("Template name is required.", "VALIDATION_ERROR", 400);
            }

            JsonNode manifestNode = args.path("manifest");
            if (manifestNode.isMissingNode() || !manifestNode.isObject()) {
                return errorJson("Manifest object is required.", "VALIDATION_ERROR", 400);
            }

            ObjectMapper tolerantMapper = objectMapper.copy();
            tolerantMapper.enable(MapperFeature.ACCEPT_CASE_INSENSITIVE_PROPERTIES);
            DeviceTemplateDto.DeviceManifest manifest = tolerantMapper.treeToValue(
                    manifestNode, DeviceTemplateDto.DeviceManifest.class);
            if (manifest == null || manifest.getModes() == null || manifest.getModes().isEmpty()) {
                return errorJson("Manifest must contain non-empty modes.", "VALIDATION_ERROR", 400);
            }
            if (manifest.getInitState() == null || manifest.getInitState().isBlank()) {
                return errorJson("Manifest must contain InitState.", "VALIDATION_ERROR", 400);
            }

            DeviceTemplateDto dto = new DeviceTemplateDto();
            dto.setName(name);
            dto.setManifest(manifest);

            DeviceTemplateDto saved = boardStorageService.addDeviceTemplate(userId, dto);
            return writeJson(Map.of(
                    "message", "Template added successfully.",
                    "templateId", saved.getId(),
                    "name", saved.getName()
            ));
        } catch (ServiceUnavailableException e) {
            log.warn("add_template busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("add_template business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("add_template failed", e);
            return errorJson("Failed to add template. Please check manifest format and retry.",
                    "INTERNAL_ERROR", 500);
        }
    }

    private String trimToNull(String value) {
        if (value == null) {
            return null;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }

    private String errorJson(String message, String errorCode, int status) {
        return AiToolResponseHelper.error(objectMapper, message, errorCode, status);
    }

    private String writeJson(Map<String, Object> body) {
        return AiToolResponseHelper.success(objectMapper, body, "Template added successfully.");
    }
}
