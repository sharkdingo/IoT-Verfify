package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.SimulationService;
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
public class CancelSimulateTaskTool extends AbstractAiTool {

    private final SimulationService simulationService;

    public CancelSimulateTaskTool(SimulationService simulationService,
                                   ObjectMapper objectMapper) {
        super(objectMapper);
        this.simulationService = simulationService;
    }

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

            boolean cancelled = simulationService.cancelTask(userId, taskId);
            return successJson(Map.of(
                    "taskId", taskId,
                    "cancelled", cancelled,
                    "message", cancelled ? "Simulation task cancelled." : "Task is not cancellable or not found."
            ), "Simulation task cancellation completed.");
        } catch (ServiceUnavailableException e) {
            log.warn("cancel_simulate_task busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("cancel_simulate_task business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("cancel_simulate_task failed", e);
            return errorJson("Failed to cancel simulation task.",
                    "INTERNAL_ERROR", 500);
        }
    }
}
