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
public class GetSimulationTraceTool extends AbstractAiTool {

    private final SimulationService simulationService;

    public GetSimulationTraceTool(SimulationService simulationService,
                                   ObjectMapper objectMapper) {
        super(objectMapper);
        this.simulationService = simulationService;
    }

    @Override
    public String getName() {
        return "get_simulation_trace";
    }

    @Override
    public ChatTool getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object",
                Map.of(
                        "simulationId", Map.of("type", "integer", "description", "Simulation trace ID."),
                        "includeRaw", Map.of("type", "boolean", "description", "Whether to include raw NuSMV output and request JSON. Default false.")
                ),
                List.of("simulationId")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Get a saved simulation trace by simulationId, including its state sequence.")
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
            boolean includeRaw = args.path("includeRaw").asBoolean(false);

            SimulationTraceDto trace = simulationService.getSimulation(userId, simulationId);

            Map<String, Object> traceBody = new LinkedHashMap<>();
            traceBody.put("id", trace.getId());
            traceBody.put("requestedSteps", trace.getRequestedSteps());
            traceBody.put("steps", trace.getSteps());
            traceBody.put("stateCount", trace.getStates() != null ? trace.getStates().size() : 0);
            traceBody.put("states", trace.getStates() == null ? List.of() : trace.getStates());
            traceBody.put("logs", trace.getLogs() == null ? List.of() : trace.getLogs());
            traceBody.put("createdAt", trace.getCreatedAt());
            if (includeRaw) {
                traceBody.put("nusmvOutput", trace.getNusmvOutput());
                traceBody.put("requestJson", trace.getRequestJson());
            }

            Map<String, Object> body = new LinkedHashMap<>();
            body.put("simulationId", simulationId);
            body.put("includeRaw", includeRaw);
            body.put("trace", traceBody);
            return successJson(body, "Simulation trace loaded.");
        } catch (ServiceUnavailableException e) {
            log.warn("get_simulation_trace busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("get_simulation_trace business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("get_simulation_trace failed", e);
            return errorJson("Failed to get simulation trace.", "INTERNAL_ERROR", 500);
        }
    }
}
