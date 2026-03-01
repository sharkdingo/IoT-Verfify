package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.List;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class CancelVerifyTaskTool implements AiTool {

    private final VerificationService verificationService;
    private final ObjectMapper objectMapper;

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
    public String execute(String argsJson) {
        try {
            Long userId = UserContextHolder.getUserId();
            if (userId == null) {
                return errorJson("User not logged in");
            }

            JsonNode args = objectMapper.readTree(argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
            if (!args.has("taskId") || !args.path("taskId").canConvertToLong()) {
                return errorJson("'taskId' is required.");
            }
            long taskId = args.path("taskId").asLong();
            if (taskId <= 0) {
                return errorJson("'taskId' must be positive.");
            }

            boolean cancelled = verificationService.cancelTask(userId, taskId);
            return objectMapper.writeValueAsString(Map.of(
                    "taskId", taskId,
                    "cancelled", cancelled,
                    "message", cancelled ? "Verification task cancelled." : "Task is not cancellable or not found."
            ));
        } catch (Exception e) {
            log.error("cancel_verify_task failed", e);
            return errorJson("Failed to cancel verification task: " + e.getMessage());
        }
    }

    private String errorJson(String message) {
        try {
            return objectMapper.writeValueAsString(Map.of("error", message));
        } catch (Exception e) {
            return "{\"error\":\"" + message + "\"}";
        }
    }
}
