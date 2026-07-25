package cn.edu.nju.Iot_Verify.component.aitool.fuzz;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.component.aitool.ModelTraceToolPresenter;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzFindingDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzInputEventDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.FuzzService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

@Slf4j
@Component
public class GetFuzzFindingTool extends AbstractAiTool {

    private final FuzzService fuzzService;

    public GetFuzzFindingTool(FuzzService fuzzService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.fuzzService = fuzzService;
    }

    @Override
    public String getName() {
        return "get_fuzz_finding";
    }

    @Override
    public LlmToolSpec getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object",
                Map.of(
                        "findingId", Map.of("type", "integer",
                                "description", "Counterexample-search finding ID (from get_fuzz_run's findings)."),
                        "stateOffset", Map.of("type", "integer",
                                "description", "Zero-based state-sequence offset, 0-10000 (default 0)."),
                        "stateLimit", Map.of("type", "integer",
                                "description", "Number of states to return, 1-20 (default 10).")),
                List.of("findingId"));
        return LlmToolSpec.of(getName(),
                "Get one counterexample-search finding, including its violated specification, first violation step, and a bounded state/input-event window. Page states with stateOffset and stateLimit. A finding is heuristic candidate evidence, not a formal counterexample; never route it into fix_violation or apply_fix.",
                schema);
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
            requireOnlyFields(args, "arguments", Set.of(
                    "findingId", "stateOffset", "stateLimit"));
            long findingId = positiveLongArg(args, "findingId");
            int stateOffset = intArgInRange(args, "stateOffset", 0, 0, 10_000);
            int stateLimit = intArgInRange(args, "stateLimit", 10, 1, 20);

            FuzzFindingDto finding = fuzzService.getFinding(userId, findingId);
            List<TraceStateDto> states = safeList(finding.getStates());
            int windowStart = Math.min(stateOffset, states.size());
            int windowEnd = Math.min(states.size(), windowStart + stateLimit);
            List<TraceStateDto> stateWindow = states.subList(windowStart, windowEnd);

            List<FuzzInputEventDto> inputEvents = safeList(finding.getInputEvents());
            List<FuzzInputEventDto> inputEventWindow = new ArrayList<>();
            for (FuzzInputEventDto event : inputEvents) {
                if (event != null && event.getStep() >= windowStart && event.getStep() < windowEnd) {
                    inputEventWindow.add(event);
                }
            }

            Map<String, Object> body = new LinkedHashMap<>();
            body.put("findingId", finding.getId());
            body.put("runId", finding.getFuzzTaskId());
            body.put("violatedSpec", ModelTraceToolPresenter.violatedSpecification(
                    finding.getViolatedSpec()));
            body.put("firstViolationStep", finding.getFirstViolationStep());
            body.put("seed", finding.getSeed());
            body.put("stateCount", states.size());
            body.put("stateOffset", stateOffset);
            body.put("stateLimit", stateLimit);
            body.put("returnedStateCount", stateWindow.size());
            body.put("hasMoreStates", windowEnd < states.size());
            if (windowEnd < states.size()) {
                body.put("nextStateOffset", windowEnd);
            }
            body.put("states", ModelTraceToolPresenter.states(stateWindow));
            body.put("inputEventCount", inputEvents.size());
            body.put("returnedInputEventCount", inputEventWindow.size());
            body.put("inputEvents", List.copyOf(inputEventWindow));
            body.put("createdAt", finding.getCreatedAt());
            body.put("message", "Counterexample-search finding loaded. This is heuristic candidate evidence, not a formal counterexample.");
            return readOnlySuccessJson(body, "Counterexample-search finding loaded.");
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
        } catch (ServiceUnavailableException e) {
            log.warn("get_fuzz_finding busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("get_fuzz_finding business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("get_fuzz_finding failed", e);
            return errorJson("Failed to get counterexample-search finding.", "INTERNAL_ERROR", 500);
        }
    }
}
