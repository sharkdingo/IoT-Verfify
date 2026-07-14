package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.model.TaskCancellationResultDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.List;
import java.util.Map;
import java.util.Set;

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
    public LlmToolSpec getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object",
                Map.of("taskId", Map.of("type", "integer", "description", "Simulation task ID.")),
                List.of("taskId")
        );

        return LlmToolSpec.of(getName(), "Cancel an async simulation task by taskId.", schema);
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
            requireOnlyFields(args, "arguments", Set.of("taskId"));
            long taskId = positiveLongArg(args, "taskId");

            TaskCancellationResultDto result = simulationService.cancelTask(userId, taskId);
            return successJson(Map.of(
                    "taskId", result.getTaskId(),
                    "cancellationAccepted", result.isCancellationAccepted(),
                    "cancellationOutcome", result.getCancellationOutcome(),
                    "taskStatus", result.getTaskStatus(),
                    "executionMayStillBeStopping", result.isExecutionMayStillBeStopping(),
                    "message", cancellationMessage(result)
            ), "Simulation task cancellation completed.");
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
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

    private static String cancellationMessage(TaskCancellationResultDto result) {
        return switch (result.getCancellationOutcome()) {
            case ACCEPTED -> result.isExecutionMayStillBeStopping()
                    ? "The task was marked CANCELLED; the running simulator may still be stopping."
                    : "The pending task was marked CANCELLED before execution.";
            case ALREADY_CANCELLED -> "The task was already marked CANCELLED.";
            case ALREADY_COMPLETED -> "The task completed before cancellation; inspect its result.";
            case ALREADY_FAILED -> "The task failed before cancellation; inspect its error.";
            case NO_LONGER_CANCELLABLE -> "The task is no longer in a cancellable state.";
        };
    }
}
