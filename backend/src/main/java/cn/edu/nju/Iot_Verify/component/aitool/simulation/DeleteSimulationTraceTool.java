package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
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

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

@Slf4j
@Component
public class DeleteSimulationTraceTool extends AbstractAiTool {

    private final SimulationService simulationService;

    public DeleteSimulationTraceTool(SimulationService simulationService,
                                      ObjectMapper objectMapper) {
        super(objectMapper);
        this.simulationService = simulationService;
    }

    @Override
    public String getName() {
        return "delete_simulation_trace";
    }

    @Override
    public ChatTool getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object",
                Map.of("simulationId", Map.of("type", "integer", "description", "Simulation trace ID.")),
                List.of("simulationId")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Delete a saved simulation trace by simulationId.")
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

            if (!args.has("simulationId") || !args.path("simulationId").canConvertToLong()) {
                return errorJson("'simulationId' is required.", "VALIDATION_ERROR", 400);
            }
            long simulationId = args.path("simulationId").asLong();
            if (simulationId <= 0) {
                return errorJson("'simulationId' must be positive.", "VALIDATION_ERROR", 400);
            }

            // Pre-check to provide explicit not-found error before deletion.
            SimulationTraceDto trace = simulationService.getSimulation(userId, simulationId);
            simulationService.deleteSimulation(userId, simulationId);

            Map<String, Object> body = new LinkedHashMap<>();
            body.put("simulationId", simulationId);
            body.put("steps", trace.getSteps());
            body.put("deleted", true);
            body.put("message", "Simulation trace deleted.");
            return successJson(body, "Simulation trace deleted.");
        } catch (ServiceUnavailableException e) {
            log.warn("delete_simulation_trace busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("delete_simulation_trace business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("delete_simulation_trace failed", e);
            return errorJson("Failed to delete simulation trace.", "INTERNAL_ERROR", 500);
        }
    }
}
