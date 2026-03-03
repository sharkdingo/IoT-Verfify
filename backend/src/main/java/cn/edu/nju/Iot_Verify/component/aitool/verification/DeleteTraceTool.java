package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class DeleteTraceTool implements AiTool {

    private final VerificationService verificationService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "delete_trace";
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
                        .description("Delete a saved verification trace by traceId.")
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

            JsonNode args;
            try {
                args = objectMapper.readTree(argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
            } catch (Exception parseEx) {
                return errorJson("Invalid JSON arguments.", "VALIDATION_ERROR", 400);
            }

            if (!args.has("traceId") || !args.path("traceId").canConvertToLong()) {
                return errorJson("'traceId' is required.", "VALIDATION_ERROR", 400);
            }
            long traceId = args.path("traceId").asLong();
            if (traceId <= 0) {
                return errorJson("'traceId' must be positive.", "VALIDATION_ERROR", 400);
            }

            // Pre-check existence because deleteTrace is idempotent in service implementation.
            TraceDto trace = verificationService.getTrace(userId, traceId);
            verificationService.deleteTrace(userId, traceId);

            Map<String, Object> body = new LinkedHashMap<>();
            body.put("traceId", traceId);
            body.put("violatedSpecId", trace.getViolatedSpecId());
            body.put("deleted", true);
            body.put("message", "Trace deleted.");
            return successJson(body, "Trace deleted.");
        } catch (ServiceUnavailableException e) {
            log.warn("delete_trace busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("delete_trace business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("delete_trace failed", e);
            return errorJson("Failed to delete trace.", "INTERNAL_ERROR", 500);
        }
    }

    private String errorJson(String message, String errorCode, int status) {
        return AiToolResponseHelper.error(objectMapper, message, errorCode, status);
    }

    private String successJson(Map<String, Object> body, String fallbackMessage) {
        return AiToolResponseHelper.success(objectMapper, body, fallbackMessage);
    }
}
