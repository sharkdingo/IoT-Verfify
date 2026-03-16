package cn.edu.nju.Iot_Verify.component.aitool.template;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.MapperFeature;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import jakarta.annotation.PostConstruct;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

@Slf4j
@Component
public class AddTemplateTool extends AbstractAiTool {

    private final BoardStorageService boardStorageService;
    private ObjectMapper tolerantMapper;

    public AddTemplateTool(BoardStorageService boardStorageService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardStorageService = boardStorageService;
    }

    @PostConstruct
    void initTolerantMapper() {
        tolerantMapper = objectMapper.copy();
        tolerantMapper.setConfig(
                tolerantMapper.getDeserializationConfig()
                        .with(MapperFeature.ACCEPT_CASE_INSENSITIVE_PROPERTIES)
        );
    }

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
                "description", "Full device manifest JSON defining the device behavior. " +
                        "For stateful devices, must include: Name, Description, Modes (array of mode dimension names), InitState (semicolon-separated for multi-mode), " +
                        "WorkingStates (array of {Name, Description, Trust, Privacy, Dynamics[]}), " +
                        "Transitions (array of {Name, StartState (optional), EndState (optional for internal variable transitions), Trigger{Attribute,Relation,Value}, Signal, Assignments[{Attribute,Value}]}), " +
                        "APIs (array of {Name, Description, StartState (optional, empty or '_' means from any state), EndState, Signal, Trigger{Attribute,Relation,Value}, Assignments[{Attribute,Value}]}). " +
                        "For stateless sensors (no modes), Modes/InitState/WorkingStates can all be empty. " +
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

    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }
            String name = trimToNull(args.path("name").asText(null));
            if (name == null) {
                return errorJson("Template name is required.", "VALIDATION_ERROR", 400);
            }

            JsonNode manifestNode = args.path("manifest");
            if (manifestNode.isMissingNode() || !manifestNode.isObject()) {
                return errorJson("Manifest object is required.", "VALIDATION_ERROR", 400);
            }

            DeviceTemplateDto.DeviceManifest manifest = tolerantMapper.treeToValue(
                    manifestNode, DeviceTemplateDto.DeviceManifest.class);
            if (manifest == null) {
                return errorJson("Manifest could not be parsed.", "VALIDATION_ERROR", 400);
            }
            // Align with backend: no-mode sensors have all three empty; otherwise all must be present
            boolean hasModes = manifest.getModes() != null && !manifest.getModes().isEmpty();
            boolean hasInitState = manifest.getInitState() != null && !manifest.getInitState().isBlank();
            boolean hasWorkingStates = manifest.getWorkingStates() != null && !manifest.getWorkingStates().isEmpty();
            if (hasModes || hasInitState || hasWorkingStates) {
                if (!hasModes) {
                    return errorJson("Manifest must contain non-empty Modes when InitState or WorkingStates are defined.", "VALIDATION_ERROR", 400);
                }
                if (!hasInitState) {
                    return errorJson("Manifest must contain InitState when Modes are defined.", "VALIDATION_ERROR", 400);
                }
                if (!hasWorkingStates) {
                    return errorJson("Manifest must contain non-empty WorkingStates when Modes are defined.", "VALIDATION_ERROR", 400);
                }
            }

            DeviceTemplateDto dto = new DeviceTemplateDto();
            dto.setName(name);
            dto.setManifest(manifest);

            DeviceTemplateDto saved = boardStorageService.addDeviceTemplate(userId, dto);
            return successJson(Map.of(
                    "message", "Template added successfully.",
                    "templateId", saved.getId(),
                    "name", saved.getName()
            ), "Template added successfully.");
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
}
