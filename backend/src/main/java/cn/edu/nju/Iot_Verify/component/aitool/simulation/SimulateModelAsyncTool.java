package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

@Slf4j
@Component
public class SimulateModelAsyncTool extends AbstractAiTool {

    private final BoardDataConverter boardDataConverter;
    private final SimulationService simulationService;

    public SimulateModelAsyncTool(BoardDataConverter boardDataConverter,
                                  SimulationService simulationService,
                                  ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardDataConverter = boardDataConverter;
        this.simulationService = simulationService;
    }

    @Override
    public String getName() {
        return "simulate_model_async";
    }

    @Override
    public LlmToolSpec getDefinition() {
        Map<String, Object> props = new LinkedHashMap<>();
        props.put("steps", Map.of("type", "integer", "description", "Number of simulation steps (1-100, rejected if outside range). Default 10."));
        props.put("isAttack", Map.of("type", "boolean", "description", "Include compromised device-instance and automation-link behavior. A device instance is a budget point only when it has a declared falsifiable reading or is a TAP command target; each submitted TAP rule's command-delivery link is another point. Inert devices are excluded. Declared falsifiable readings may vary within their domains; once a target or automation link is selected as compromised, that command is dropped. Other device-internal transitions are not frozen. Default false."));
        props.put("attackBudget", Map.of("type", "integer", "description", "Maximum compromised behavior-changing device-instance or automation-link points (1-50 when attack modeling is enabled, and no more than the effective attack surface returned by the model). Simulation returns one possible trajectory within this upper bound, not coverage of every combination. Omit it or use 0 when attack modeling is disabled; a positive disabled budget is rejected. Default 1 when enabled."));
        props.put("enablePrivacy", Map.of("type", "boolean", "description", "Track private-data labels through automation chains. This is not access control or encryption. Default false."));

        FunctionParameterSchema schema = new FunctionParameterSchema("object", props, Collections.emptyList());

        return LlmToolSpec.of(getName(), "Submit an async NuSMV simulation task. Returns its authoritative current task status, progress, frozen model snapshot, and taskId for later polling; acceptance does not mean simulation completed.", schema);
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
                    "steps", "isAttack", "attackBudget", "enablePrivacy"));
            int steps = intArgInRange(args, "steps", 10, 1, 100);
            boolean isAttack = booleanArg(args, "isAttack", false);
            int attackBudget = attackBudgetArg(args, isAttack);
            boolean enablePrivacy = booleanArg(args, "enablePrivacy", false);

            ModelInputSnapshot board = boardDataConverter.getModelInputSnapshot(userId);
            List<DeviceVerificationDto> devices = board.devices();
            List<RuleDto> rules = board.rules();

            if (devices.isEmpty()) {
                return errorJson("No devices found on the board. Please add devices first.",
                        "VALIDATION_ERROR", 400);
            }

            SimulationRequestDto request = new SimulationRequestDto();
            request.setDevices(devices);
            request.setEnvironmentVariables(board.environmentVariables());
            request.setRules(rules);
            request.setSteps(steps);
            request.setAttack(isAttack);
            request.setAttackBudget(attackBudget);
            request.setEnablePrivacy(enablePrivacy);
            Long taskId = simulationService.submitSimulationWithTemplateSnapshot(
                    userId, request, board.templateManifests());
            var task = simulationService.getTask(userId, taskId);

            Map<String, Object> response = new java.util.LinkedHashMap<>();
            response.put("message", "Simulation task accepted. Its current status is authoritative; completion is not implied.");
            response.put("taskId", task.getId());
            response.put("taskStatus", task.getStatus());
            response.put("progress", task.getProgress());
            response.put("requestedSteps", task.getRequestedSteps());
            response.put("isAttack", task.getIsAttack());
            response.put("attackBudget", task.getAttackBudget());
            response.put("enablePrivacy", task.getEnablePrivacy());
            response.put("modelSnapshot", task.getModelSnapshot());
            response.put("modelSemantics", task.getModelSemantics());
            return successJson(response, "Simulation task accepted.");
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
        } catch (ServiceUnavailableException e) {
            log.warn("simulate_model_async busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (SmvGenerationException e) {
            log.warn("simulate_model_async generation failed [{}]: {}", e.getErrorCategory(), e.getMessage());
            return errorJson(e.getMessage(),
                    "SMV_GENERATION_ERROR",
                    500,
                    Map.of("errorCategory", e.getErrorCategory()));
        } catch (BaseException e) {
            log.warn("simulate_model_async business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("simulate_model_async failed", e);
            return errorJson("Failed to start simulation task.",
                    "INTERNAL_ERROR", 500);
        }
    }
}
