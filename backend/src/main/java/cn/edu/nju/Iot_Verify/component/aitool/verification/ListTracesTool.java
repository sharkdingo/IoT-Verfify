package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

@Slf4j
@Component
public class ListTracesTool extends AbstractAiTool {

    private final VerificationService verificationService;

    public ListTracesTool(VerificationService verificationService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.verificationService = verificationService;
    }

    @Override
    public String getName() {
        return "list_traces";
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
                        .description("List all saved verification counterexample traces. " +
                                "Traces are automatically saved when verification finds property violations. " +
                                "Each trace shows a sequence of states leading to the violation.")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    protected String doExecute(Long userId, String argsJson) {
        try {
            List<TraceDto> traces = verificationService.getUserTraces(userId);
            if (traces.isEmpty()) {
                return objectMapper.writeValueAsString(Map.of(
                        "message", "No verification traces found. Traces are created when verification detects property violations.",
                        "count", 0
                ));
            }

            List<Map<String, Object>> summaries = traces.stream().map(t -> {
                Map<String, Object> s = new LinkedHashMap<>();
                s.put("id", t.getId());
                s.put("violatedSpecId", t.getViolatedSpecId());
                s.put("stateCount", t.getStates() != null ? t.getStates().size() : 0);
                s.put("createdAt", t.getCreatedAt());
                return s;
            }).toList();

            return objectMapper.writeValueAsString(Map.of(
                    "count", traces.size(),
                    "traces", summaries
            ));
        } catch (ServiceUnavailableException e) {
            log.warn("list_traces busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("list_traces business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("list_traces failed", e);
            return errorJson("Failed to list traces.", "INTERNAL_ERROR", 500);
        }
    }
}
