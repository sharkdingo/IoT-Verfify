package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.component.aitool.BoardDataHelper;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationResultDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class SimulateModelTool implements AiTool {

    private final BoardDataHelper boardDataHelper;
    private final BoardStorageService boardStorageService;
    private final SimulationService simulationService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "simulate_model";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("steps", Map.of(
                "type", "integer",
                "description", "Number of simulation steps (1-100). Default 10."
        ));
        props.put("isAttack", Map.of(
                "type", "boolean",
                "description", "Enable attack mode. Default false."
        ));
        props.put("intensity", Map.of(
                "type", "integer",
                "description", "Attack intensity (0-50). Only effective when isAttack=true. Default 3."
        ));
        props.put("enablePrivacy", Map.of(
                "type", "boolean",
                "description", "Enable privacy dimension modeling. Default false."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Run NuSMV random simulation on the current board. " +
                                "Automatically reads all devices and rules from the board. " +
                                "Returns a sequence of states showing how the system evolves over N steps. " +
                                "Requires at least one device on the board.")
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
            int steps = args.path("steps").asInt(10);
            boolean isAttack = args.path("isAttack").asBoolean(false);
            int intensity = args.path("intensity").asInt(3);
            boolean enablePrivacy = args.path("enablePrivacy").asBoolean(false);

            // Clamp numeric ranges to avoid extreme execution parameters.
            steps = Math.max(1, Math.min(100, steps));
            intensity = Math.max(0, Math.min(50, intensity));

            // Load board data directly from current workspace state.
            List<DeviceVerificationDto> devices = boardDataHelper.getDevicesForVerification(userId);
            List<RuleDto> rules = safeList(boardStorageService.getRules(userId));

            if (devices.isEmpty()) {
                return errorJson("No devices found on the board. Please add devices first.",
                        "VALIDATION_ERROR", 400);
            }

            log.info("Executing simulate_model: {} devices, {} rules, {} steps, attack={}, intensity={}, privacy={}",
                    devices.size(), rules.size(), steps, isAttack, intensity, enablePrivacy);

            SimulationResultDto result = simulationService.simulate(
                    userId, devices, rules, steps, isAttack, intensity, enablePrivacy);

            // Build a compact summary for chat output.
            Map<String, Object> summary = new LinkedHashMap<>();
            summary.put("requestedSteps", result.getRequestedSteps());
            summary.put("actualSteps", result.getSteps());
            summary.put("stateCount", result.getStates() != null ? result.getStates().size() : 0);

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

            return successJson(summary, "Simulation completed.");
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

    private <T> List<T> safeList(List<T> list) {
        return list == null ? List.of() : list;
    }

    private String errorJson(String message, String errorCode, int status) {
        return errorJson(message, errorCode, status, Map.of());
    }

    private String errorJson(String message, String errorCode, int status, Map<String, Object> extras) {
        return AiToolResponseHelper.error(objectMapper, message, errorCode, status, extras);
    }

    private String successJson(Map<String, Object> body, String fallbackMessage) {
        return AiToolResponseHelper.success(objectMapper, body, fallbackMessage);
    }
}
