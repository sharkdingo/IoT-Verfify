package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.extern.slf4j.Slf4j;
import org.springframework.core.task.TaskRejectedException;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

@Slf4j
@Component
public class SimulateModelAsyncTool extends AbstractAiTool {

    private final BoardDataConverter boardDataConverter;
    private final BoardStorageService boardStorageService;
    private final SimulationService simulationService;

    public SimulateModelAsyncTool(BoardDataConverter boardDataConverter,
                                  BoardStorageService boardStorageService,
                                  SimulationService simulationService,
                                  ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardDataConverter = boardDataConverter;
        this.boardStorageService = boardStorageService;
        this.simulationService = simulationService;
    }

    @Override
    public String getName() {
        return "simulate_model_async";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new LinkedHashMap<>();
        props.put("steps", Map.of("type", "integer", "description", "Number of simulation steps (1-100). Default 10."));
        props.put("isAttack", Map.of("type", "boolean", "description", "Enable attack mode. Default false."));
        props.put("intensity", Map.of("type", "integer", "description", "Attack intensity (0-50). Default 3."));
        props.put("enablePrivacy", Map.of("type", "boolean", "description", "Enable privacy dimension modeling. Default false."));

        FunctionParameterSchema schema = new FunctionParameterSchema("object", props, Collections.emptyList());

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Start an async NuSMV simulation task. Returns taskId for later polling.")
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
            int steps = Math.max(1, Math.min(100, args.path("steps").asInt(10)));
            boolean isAttack = args.path("isAttack").asBoolean(false);
            int intensity = Math.max(0, Math.min(50, args.path("intensity").asInt(3)));
            boolean enablePrivacy = args.path("enablePrivacy").asBoolean(false);

            List<DeviceVerificationDto> devices = boardDataConverter.getDevicesForVerification(userId);
            List<RuleDto> rules = safeList(boardStorageService.getRules(userId));

            if (devices.isEmpty()) {
                return errorJson("No devices found on the board. Please add devices first.",
                        "VALIDATION_ERROR", 400);
            }

            Long taskId = simulationService.createTask(userId, steps);
            try {
                SimulationRequestDto request = new SimulationRequestDto();
                request.setDevices(devices);
                request.setRules(rules);
                request.setSteps(steps);
                request.setAttack(isAttack);
                request.setIntensity(intensity);
                request.setEnablePrivacy(enablePrivacy);
                simulationService.simulateAsync(userId, taskId, request);
            } catch (TaskRejectedException e) {
                simulationService.failTaskById(taskId, "Server busy, please try again later");
                return errorJson("Simulation task queue is full. Please retry later.",
                        "SERVICE_UNAVAILABLE", 503);
            } catch (Exception e) {
                simulationService.failTaskById(taskId, "Failed to dispatch: " + e.getMessage());
                throw e;
            }

            return successJson(Map.of(
                    "message", "Simulation task started.",
                    "taskId", taskId,
                    "taskStatus", "PENDING",
                    "progress", 0,
                    "requestedSteps", steps
            ), "Simulation task started.");
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
