package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.VerificationService;
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
public class GetTraceTool extends AbstractAiTool {

    private final VerificationService verificationService;

    public GetTraceTool(VerificationService verificationService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.verificationService = verificationService;
    }

    @Override
    public String getName() {
        return "get_trace";
    }

    @Override
    public ChatTool getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object",
                Map.of("traceId", Map.of("type", "integer", "description", "Verification trace ID.")),
                List.of("traceId")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Get a saved verification trace by traceId, including its state sequence.")
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

            if (!args.has("traceId") || !args.path("traceId").canConvertToLong()) {
                return errorJson("'traceId' is required.", "VALIDATION_ERROR", 400);
            }
            long traceId = args.path("traceId").asLong();
            if (traceId <= 0) {
                return errorJson("'traceId' must be positive.", "VALIDATION_ERROR", 400);
            }

            TraceDto trace = verificationService.getTrace(userId, traceId);

            Map<String, Object> body = new LinkedHashMap<>();
            body.put("traceId", traceId);
            body.put("violatedSpecId", trace.getViolatedSpecId());
            body.put("stateCount", trace.getStates() != null ? trace.getStates().size() : 0);
            body.put("trace", trace);
            return successJson(body, "Trace loaded.");
        } catch (ServiceUnavailableException e) {
            log.warn("get_trace busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("get_trace business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("get_trace failed", e);
            return errorJson("Failed to get trace.", "INTERNAL_ERROR", 500);
        }
    }
}
