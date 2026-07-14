package cn.edu.nju.Iot_Verify.component.aitool.template;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDeletionResultDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.TemplateDeletionConflictException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
    public LlmToolSpec getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("templateId", Map.of(
                "type", "integer",
                "description", "The numeric ID of the template to delete (from list_templates result)."
        ));
        props.put("confirmed", Map.of(
                "type", "boolean",
                "description", "Use false to preview the exact template without changing it. Use true only in a later turn after the user explicitly confirms that preview."
        ));
        props.put("impactToken", Map.of(
                "type", "string",
                "description", "Exact impactToken returned by the latest deletion preview. Required when confirmed=true."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, List.of("templateId", "confirmed")
        );

        return LlmToolSpec.of(getName(), "Preview or, after explicit two-turn confirmation, delete a device template. Use list_templates first.", schema);
    }

    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }
            requireOnlyFields(args, "arguments", Set.of("templateId", "confirmed", "impactToken"));
            long templateId = positiveLongArg(args, "templateId");
            boolean confirmed = booleanArg(args, "confirmed", false);
            if (!confirmed || !UserContextHolder.isDestructiveActionConfirmed()) {
                DeviceTemplateDeletionResultDto preview =
                        boardStorageService.previewDeviceTemplateDeletion(userId, templateId);
                Map<String, Object> response = new LinkedHashMap<>();
                response.put("message", preview.isCanDelete()
                        ? "No changes were made. Confirm this exact preview to delete the device type."
                        : "No changes were made. This device type cannot be deleted while listed device instances use it.");
                response.put("requiresUserConfirmation", preview.isCanDelete());
                response.put("preview", preview);
                return readOnlySuccessJson(response, "Template deletion preview unavailable.");
            }

            String impactToken = requiredTextField(args, "impactToken", "arguments");
            DeviceTemplateDeletionResultDto deleted =
                    boardStorageService.deleteDeviceTemplate(userId, templateId, impactToken);
            return successJson(Map.of(
                    "message", "Template deleted successfully.",
                    "operation", "deleted",
                    "result", deleted
            ), "Template deleted successfully.");
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
        } catch (ServiceUnavailableException e) {
            log.warn("delete_template busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (TemplateDeletionConflictException e) {
            log.warn("delete_template conflict [{}]", e.getReasonCode());
            return errorJson(e.getMessage(), e.getReasonCode(), 409,
                    Map.of("currentPreview", e.getCurrentPreview()));
        } catch (BaseException e) {
            log.warn("delete_template business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("delete_template failed", e);
            return errorJson("Failed to delete template.", "INTERNAL_ERROR", 500);
        }
    }
}
