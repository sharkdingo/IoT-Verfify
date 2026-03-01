package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.SimulationService;
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
public class CancelSimulateTaskTool implements AiTool {

    private final SimulationService simulationService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "cancel_simulate_task";
    }

    @Override
    public ChatTool getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object",
                Map.of("taskId", Map.of("type", "integer", "description", "Simulation task ID.")),
                List.of("taskId")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Cancel an async simulation task by taskId.")
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

            boolean cancelled = simulationService.cancelTask(userId, taskId);
            return objectMapper.writeValueAsString(Map.of(
                    "taskId", taskId,
                    "cancelled", cancelled,
                    "message", cancelled ? "Simulation task cancelled." : "Task is not cancellable or not found."
            ));
        } catch (Exception e) {
            log.error("cancel_simulate_task failed", e);
            return errorJson("Failed to cancel simulation task: " + e.getMessage());
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
