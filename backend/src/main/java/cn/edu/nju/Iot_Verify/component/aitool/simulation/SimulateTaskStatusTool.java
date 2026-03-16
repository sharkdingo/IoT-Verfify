package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskDto;
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
public class SimulateTaskStatusTool extends AbstractAiTool {

    private final SimulationService simulationService;

    public SimulateTaskStatusTool(SimulationService simulationService,
                                  ObjectMapper objectMapper) {
        super(objectMapper);
        this.simulationService = simulationService;
    }

    @Override
    public String getName() {
        return "simulate_task_status";
    }

    @Override
    public ChatTool getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object",
                Map.of("taskId", Map.of("type", "integer", "description", "Simulation task ID returned by simulate_model_async.")),
                List.of("taskId")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Query async simulation task status and progress by taskId.")
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

            SimulationTaskDto task = simulationService.getTask(userId, taskId);
            int progress = simulationService.getTaskProgress(userId, taskId);

            return successJson(Map.of(
                    "taskId", taskId,
                    "progress", progress,
                    "task", task
            ), "Simulation task status retrieved.");
        } catch (ServiceUnavailableException e) {
            log.warn("simulate_task_status busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("simulate_task_status business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("simulate_task_status failed", e);
            return errorJson("Failed to query simulation task.",
                    "INTERNAL_ERROR", 500);
        }
    }
}
