package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.service.FixService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

@Slf4j
@Component
public class FixViolationTool extends AbstractAiTool {

    private final FixService fixService;

    public FixViolationTool(FixService fixService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.fixService = fixService;
    }

    @Override
    public String getName() {
        return "fix_violation";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new LinkedHashMap<>();

        props.put("traceId", Map.of(
                "type", "integer",
                "description", "ID of the violation trace to fix. Obtained from verify_model result."
        ));
        props.put("strategies", Map.of(
                "type", "array",
                "description", "Fix strategies to attempt, in order. Supported: 'parameter' (§5.1 threshold adjustment), "
                        + "'condition' (§5.2 triggering condition adjustment), 'disable' (rule disabling). "
                        + "Default: ['parameter', 'condition', 'disable'].",
                "items", Map.of("type", "string")
        ));
        props.put("preferredRanges", Map.of(
                "type", "object",
                "description", "Optional per-parameter preferred value ranges. "
                        + "Keys are 'r{ruleIdx}_c{condIdx}' (e.g. 'r0_c1'). "
                        + "Values are objects with 'lower' (int) and 'upper' (int) fields.",
                "additionalProperties", Map.of(
                        "type", "object",
                        "properties", Map.of(
                                "lower", Map.of("type", "integer", "description", "Lower bound (inclusive)"),
                                "upper", Map.of("type", "integer", "description", "Upper bound (inclusive)")
                        ),
                        "required", List.of("lower", "upper")
                )
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, List.of("traceId")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Analyze a violation trace to localize fault rules and suggest fixes. " +
                                "Supports 'parameter' (adjust numeric thresholds), 'condition' (remove triggering conditions), " +
                                "and 'disable' (disable entire rules) strategies. Requires a traceId from a previous verification.")
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

            if (!args.has("traceId") || args.get("traceId").isNull()) {
                return errorJson("traceId is required.", "VALIDATION_ERROR", 400);
            }
            if (!args.get("traceId").isIntegralNumber()) {
                return errorJson("traceId must be an integer.", "VALIDATION_ERROR", 400);
            }
            if (!args.get("traceId").canConvertToLong()) {
                return errorJson("traceId is out of range.", "VALIDATION_ERROR", 400);
            }
            long traceId = args.get("traceId").asLong();

            List<String> strategies = new ArrayList<>();
            if (args.has("strategies") && args.get("strategies").isArray()) {
                for (JsonNode s : args.get("strategies")) {
                    strategies.add(s.asText());
                }
            }
            if (strategies.isEmpty()) {
                strategies = null; // use RuleFixer default order
            }

            // Parse preferredRanges (strict validation, fail-fast on invalid input)
            Map<String, PreferredRange> preferredRanges = null;
            if (args.has("preferredRanges")) {
                JsonNode prNode = args.get("preferredRanges");
                if (!prNode.isObject()) {
                    return errorJson("preferredRanges must be an object.", "VALIDATION_ERROR", 400);
                }
                preferredRanges = new LinkedHashMap<>();
                for (Map.Entry<String, JsonNode> entry : prNode.properties()) {
                    String key = entry.getKey();
                    if (!key.matches("r\\d+_c\\d+")) {
                        return errorJson("preferredRanges key '" + key
                                + "' must match 'r{ruleIdx}_c{condIdx}' (e.g. 'r0_c1').", "VALIDATION_ERROR", 400);
                    }
                    JsonNode val = entry.getValue();
                    if (!val.has("lower") || !val.has("upper")) {
                        return errorJson("preferredRanges entry '" + key
                                + "' missing 'lower' or 'upper'.", "VALIDATION_ERROR", 400);
                    }
                    if (!val.get("lower").isIntegralNumber() || !val.get("upper").isIntegralNumber()) {
                        return errorJson("preferredRanges entry '" + key
                                + "': 'lower' and 'upper' must be integers.", "VALIDATION_ERROR", 400);
                    }
                    int lower = val.get("lower").intValue();
                    int upper = val.get("upper").intValue();
                    if (lower > upper) {
                        return errorJson("preferredRanges entry '" + key
                                + "': lower(" + lower + ") > upper(" + upper + ").", "VALIDATION_ERROR", 400);
                    }
                    preferredRanges.put(key, new PreferredRange(lower, upper));
                }
                if (preferredRanges.isEmpty()) preferredRanges = null;
            }

            FixResultDto result = fixService.fix(userId, traceId, strategies, preferredRanges);

            Map<String, Object> summary = new LinkedHashMap<>();
            summary.put("traceId", result.getTraceId());
            summary.put("violatedSpecId", result.getViolatedSpecId());
            summary.put("fixable", result.isFixable());
            summary.put("faultRuleCount", result.getFaultRules() != null ? result.getFaultRules().size() : 0);
            summary.put("suggestionCount", result.getSuggestions() != null ? result.getSuggestions().size() : 0);
            summary.put("summary", result.getSummary());

            if (result.getFaultRules() != null && !result.getFaultRules().isEmpty()) {
                summary.put("faultRules", result.getFaultRules());
            }
            if (result.getSuggestions() != null && !result.getSuggestions().isEmpty()) {
                summary.put("suggestions", result.getSuggestions());
            }
            if (result.getUnusedPreferredRangeKeys() != null && !result.getUnusedPreferredRangeKeys().isEmpty()) {
                summary.put("unusedPreferredRangeKeys", result.getUnusedPreferredRangeKeys());
            }

            return successJson(summary, "Fix analysis completed.");

        } catch (ResourceNotFoundException e) {
            return errorJson("Trace not found: " + e.getMessage(), "NOT_FOUND", 404);
        } catch (BadRequestException e) {
            return errorJson(e.getMessage(), "BAD_REQUEST", 400);
        } catch (ServiceUnavailableException e) {
            log.warn("fix_violation busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (SmvGenerationException e) {
            log.warn("fix_violation generation failed [{}]: {}", e.getErrorCategory(), e.getMessage());
            return errorJson(e.getMessage(),
                    "SMV_GENERATION_ERROR",
                    500,
                    Map.of("errorCategory", e.getErrorCategory()));
        } catch (BaseException e) {
            log.warn("fix_violation business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("FixViolationTool execution failed", e);
            return errorJson("Fix analysis failed.", "INTERNAL_ERROR", 500);
        }
    }
}
