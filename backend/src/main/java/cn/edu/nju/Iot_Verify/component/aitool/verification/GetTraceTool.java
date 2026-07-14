package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.component.aitool.ModelTraceToolPresenter;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
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
    public LlmToolSpec getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object",
                Map.of("traceId", Map.of("type", "integer", "description", "Verification trace ID.")),
                List.of("traceId")
        );

        return LlmToolSpec.of(getName(), "Get a saved verification trace by traceId, including its state sequence.", schema);
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

            requireOnlyFields(args, "arguments", Set.of("traceId"));
            long traceId = positiveLongArg(args, "traceId");

            TraceDto trace = verificationService.getTrace(userId, traceId);

            Map<String, Object> body = new LinkedHashMap<>();
            body.put("traceId", traceId);
            body.put("violatedSpecification", ModelTraceToolPresenter.violatedSpecification(trace));
            body.put("modelComplete", trace.getModelComplete());
            body.put("disabledRuleCount", trace.getDisabledRuleCount());
            body.put("skippedSpecCount", trace.getSkippedSpecCount());
            body.put("generationIssues", trace.getGenerationIssues());
            body.put("stateCount", trace.getStates() != null ? trace.getStates().size() : 0);
            body.put("states", ModelTraceToolPresenter.states(trace.getStates()));
            body.put("isAttack", trace.getAttack());
            body.put("attackBudget", trace.getAttackBudget());
            body.put("enablePrivacy", trace.getEnablePrivacy());
            body.put("modelSemantics", trace.getModelSemantics());
            body.put("modelSnapshot", trace.getModelSnapshot());
            body.put("createdAt", trace.getCreatedAt());
            String message = Boolean.FALSE.equals(trace.getModelComplete())
                    ? "Counterexample trace loaded, but its source verification used an incomplete generated model."
                    : "Counterexample trace loaded from its saved model snapshot.";
            body.put("message", message);
            return readOnlySuccessJson(body, message);
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
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
