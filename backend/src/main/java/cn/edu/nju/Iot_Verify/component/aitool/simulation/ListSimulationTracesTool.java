package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class ListSimulationTracesTool implements AiTool {

    private final SimulationService simulationService;
    private final ObjectMapper objectMapper;

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
    public String execute(String argsJson) {
        try {
            Long userId = UserContextHolder.getUserId();
            if (userId == null) {
                return errorJson("User not logged in", "UNAUTHORIZED", 401);
            }

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

    private String errorJson(String message, String errorCode, int status) {
        return AiToolResponseHelper.error(objectMapper, message, errorCode, status);
    }
}
