package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.List;
import java.util.Map;

@Slf4j
@Component
public class CancelVerifyTaskTool extends AbstractAiTool {

    private final VerificationService verificationService;

    public CancelVerifyTaskTool(VerificationService verificationService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.verificationService = verificationService;
    }

    @Override
    public String getName() {
        return "cancel_verify_task";
    }

    @Override
    public ChatTool getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object",
                Map.of("taskId", Map.of("type", "integer", "description", "Verification task ID.")),
                List.of("taskId")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Cancel an async verification task by taskId.")
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
            if (!args.has("taskId") || !args.path("taskId").canConvertToLong()) {
                return errorJson("'taskId' is required.", "VALIDATION_ERROR", 400);
            }
            long taskId = args.path("taskId").asLong();
            if (taskId <= 0) {
                return errorJson("'taskId' must be positive.", "VALIDATION_ERROR", 400);
            }

            boolean cancelled = verificationService.cancelTask(userId, taskId);
            return successJson(Map.of(
                    "taskId", taskId,
                    "cancelled", cancelled,
                    "message", cancelled ? "Verification task cancelled." : "Task is not cancellable or not found."
            ), "Verification task cancellation completed.");
        } catch (ServiceUnavailableException e) {
            log.warn("cancel_verify_task busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("cancel_verify_task business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("cancel_verify_task failed", e);
            return errorJson("Failed to cancel verification task.",
                    "INTERNAL_ERROR", 500);
        }
    }
}
