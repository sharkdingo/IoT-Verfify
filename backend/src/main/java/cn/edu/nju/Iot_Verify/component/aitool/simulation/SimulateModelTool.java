package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationResultDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SimulationExecutionException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

@Slf4j
@Component
public class SimulateModelTool extends AbstractAiTool {

    private final BoardDataConverter boardDataConverter;
    private final SimulationService simulationService;

    public SimulateModelTool(BoardDataConverter boardDataConverter,
                             SimulationService simulationService,
                             ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardDataConverter = boardDataConverter;
        this.simulationService = simulationService;
    }

    @Override
    public String getName() {
        return "simulate_model";
    }

    @Override
    public LlmToolSpec getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("steps", Map.of(
                "type", "integer",
                "description", "Number of simulation steps (1-100, rejected if outside range). Default 10."
        ));
        props.put("attackMode", Map.of(
                "type", "string", "enum", List.of("none", "exact"),
                "description", "Per-run attack selection. Simulation requires explicit points and never chooses attack points randomly. Default none."));
        props.put("attackPoints", attackPointsSchema());
        props.put("enablePrivacy", Map.of(
                "type", "boolean",
                "description", "Track private-data labels through automation chains. This models label propagation, not access control or encryption. Default false."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return LlmToolSpec.of(getName(), "Run NuSMV random simulation on the current board. " +
                "Atomically snapshots all devices, environment values, rules, and referenced templates from the board. " +
                "Returns a sequence of states showing how the system evolves over N steps. " +
                "Requires at least one device on the board.", schema);
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
                    "steps", "attackMode", "attackPoints", "enablePrivacy"));
            int steps = intArgInRange(args, "steps", 10, 1, 100);
            AttackScenarioDto attackScenario = attackScenarioArg(args, false);
            boolean enablePrivacy = booleanArg(args, "enablePrivacy", false);

            ModelInputSnapshot board = boardDataConverter.getModelInputSnapshot(userId);
            List<DeviceVerificationDto> devices = board.devices();
            List<RuleDto> rules = board.rules();

            if (devices.isEmpty()) {
                return errorJson("No devices found on the board. Please add devices first.",
                        "VALIDATION_ERROR", 400);
            }

            log.info("Executing simulate_model: {} devices, {} rules, {} steps, attackMode={}, attackPoints={}, privacy={}",
                    devices.size(), rules.size(), steps, attackScenario.getMode(),
                    attackScenario.effectiveBudget(), enablePrivacy);

            SimulationRequestDto request = new SimulationRequestDto();
            request.setDevices(devices);
            request.setEnvironmentVariables(board.environmentVariables());
            request.setRules(rules);
            request.setSteps(steps);
            request.setAttackScenario(attackScenario);
            request.setEnablePrivacy(enablePrivacy);

            SimulationResultDto result = simulationService.simulateWithTemplateSnapshot(
                    userId, request, board.templateManifests());
            if (result == null || result.getStates() == null || result.getStates().isEmpty()) {
                throw SimulationExecutionException.fromResult(result);
            }

            // Build a compact summary for chat output.
            Map<String, Object> summary = new LinkedHashMap<>();
            summary.put("modelComplete", result.isModelComplete());
            summary.put("disabledRuleCount", result.getDisabledRuleCount());
            summary.put("generationIssues", result.getGenerationIssues());
            summary.put("requestedSteps", result.getRequestedSteps());
            summary.put("actualSteps", result.getSteps());
            summary.put("stateCount", result.getStates() != null ? result.getStates().size() : 0);
            summary.put("isAttack", Boolean.TRUE.equals(result.getIsAttack()));
            summary.put("attackBudget", result.getAttackBudget());
            summary.put("attackScenario", attackScenario);
            summary.put("enablePrivacy", result.isEnablePrivacy());
            summary.put("modelSemantics", result.getModelSemantics());
            summary.put("modelSnapshot", result.getModelSnapshot());
            summary.put("historyPersistence", result.getHistoryPersistence());

            // Include state transition overview (initial/final, and all for short traces).
            if (result.getStates() != null && !result.getStates().isEmpty()) {
                summary.put("initialState", result.getStates().get(0));
                if (result.getStates().size() > 1) {
                    summary.put("finalState", result.getStates().get(result.getStates().size() - 1));
                }
                if (result.getStates().size() <= 11) {
                    summary.put("allStates", result.getStates());
                }
            }

            if (result.getLogs() != null && !result.getLogs().isEmpty()) {
                summary.put("logs", result.getLogs());
            }

            String message = result.isModelComplete()
                    ? "Model-trace simulation completed. This is model behavior, not a prediction of the physical home."
                    : "Model-trace simulation completed with disabled rules; the trace represents an incomplete generated model.";
            message += " This preview was not added to run history.";
            summary.put("message", message);
            return readOnlySuccessJson(summary, message);
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
        } catch (SimulationExecutionException e) {
            log.warn("simulate_model produced no trace [{}]: {}", e.getReasonCode(), e.getMessage());
            return errorJson(e.getMessage(), "SIMULATION_FAILED", e.getCode(), Map.of(
                    "reasonCode", e.getReasonCode(),
                    "logs", e.getLogs()
            ));
        } catch (ServiceUnavailableException e) {
            log.warn("simulate_model busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (SmvGenerationException e) {
            log.warn("simulate_model generation failed [{}]: {}", e.getErrorCategory(), e.getMessage());
            return errorJson(e.getMessage(),
                    "SMV_GENERATION_ERROR",
                    500,
                    Map.of("errorCategory", e.getErrorCategory()));
        } catch (BaseException e) {
            log.warn("simulate_model business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("simulate_model failed", e);
            return errorJson("Simulation failed.", "INTERNAL_ERROR", 500);
        }
    }

    private Map<String, Object> attackPointsSchema() {
        return Map.of(
                "type", "array",
                "description", "Required for attackMode exact. Device ids use canonical board_overview ids and are normalized at the model boundary; automation links use persisted rule ids.",
                "items", Map.of(
                        "type", "object",
                        "properties", Map.of(
                                "kind", Map.of("type", "string", "enum", List.of("device", "automation_link")),
                                "deviceId", Map.of("type", "string"),
                                "ruleId", Map.of("type", "integer")),
                        "required", List.of("kind"),
                        "additionalProperties", false));
    }
}
