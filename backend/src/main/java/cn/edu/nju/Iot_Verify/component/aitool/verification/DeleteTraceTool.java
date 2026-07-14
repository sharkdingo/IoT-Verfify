package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.component.aitool.ModelTraceToolPresenter;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

@Slf4j
@Component
public class DeleteTraceTool extends AbstractAiTool {

    private final VerificationService verificationService;

    public DeleteTraceTool(VerificationService verificationService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.verificationService = verificationService;
    }

    @Override
    public String getName() {
        return "delete_trace";
    }

    @Override
    public LlmToolSpec getDefinition() {
        Map<String, Object> properties = new LinkedHashMap<>();
        properties.put("traceId", Map.of("type", "integer", "description", "Verification trace ID."));
        properties.put("confirmed", Map.of(
                "type", "boolean",
                "description", "Use false to preview the trace. Use true only in a later turn after explicit user confirmation."
        ));
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object",
                properties,
                List.of("traceId", "confirmed")
        );

        return LlmToolSpec.of(getName(), "Preview or, after explicit two-turn confirmation, delete a saved verification trace.", schema);
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

            requireOnlyFields(args, "arguments", Set.of("traceId", "confirmed"));
            long traceId = positiveLongArg(args, "traceId");

            TraceDto trace = verificationService.getTrace(userId, traceId);
            boolean confirmed = booleanArg(args, "confirmed", false);
            if (!confirmed || !UserContextHolder.isDestructiveActionConfirmed()) {
                Map<String, Object> preview = new LinkedHashMap<>();
                preview.put("message", "No changes were made. Explicit user confirmation is required before deleting this saved verification trace.");
                preview.put("operation", "preview");
                preview.put("requiresUserConfirmation", true);
                preview.put("traceId", traceId);
                preview.put("violatedSpecification", ModelTraceToolPresenter.violatedSpecification(trace));
                preview.put("stateCount", safeList(trace.getStates()).size());
                return readOnlySuccessJson(preview, "Verification trace deletion preview prepared; no changes were made.");
            }

            verificationService.deleteTrace(userId, traceId);

            Map<String, Object> body = new LinkedHashMap<>();
            body.put("traceId", traceId);
            body.put("violatedSpecification", ModelTraceToolPresenter.violatedSpecification(trace));
            body.put("deleted", true);
            body.put("message", "Trace deleted.");
            return successJson(body, "Trace deleted.");
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
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
}
