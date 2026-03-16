package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

@Slf4j
@Component
public class ListSimulationTracesTool extends AbstractAiTool {

    private final SimulationService simulationService;

    public ListSimulationTracesTool(SimulationService simulationService,
                                    ObjectMapper objectMapper) {
        super(objectMapper);
        this.simulationService = simulationService;
    }

    @Override
    public String getName() {
        return "list_simulation_traces";
    }

    @Override
    public ChatTool getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", Collections.emptyMap(), Collections.emptyList()
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("List all saved simulation traces for the current user.")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    protected String doExecute(Long userId, String argsJson) {
        try {
            List<SimulationTraceSummaryDto> traces = simulationService.getUserSimulations(userId);
            if (traces == null) {
                traces = List.of();
            }
            if (traces.isEmpty()) {
                return objectMapper.writeValueAsString(Map.of(
                        "message", "No simulation traces found. Run and save a simulation first.",
                        "count", 0
                ));
            }

            List<Map<String, Object>> summaries = traces.stream().map(t -> {
                Map<String, Object> s = new LinkedHashMap<>();
                s.put("id", t.getId());
                s.put("requestedSteps", t.getRequestedSteps());
                s.put("steps", t.getSteps());
                s.put("createdAt", t.getCreatedAt());
                return s;
            }).toList();

            return objectMapper.writeValueAsString(Map.of(
                    "count", traces.size(),
                    "traces", summaries
            ));
        } catch (ServiceUnavailableException e) {
            log.warn("list_simulation_traces busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("list_simulation_traces business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("list_simulation_traces failed", e);
            return errorJson("Failed to list simulation traces.", "INTERNAL_ERROR", 500);
        }
    }
}
