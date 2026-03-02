package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.component.aitool.BoardDataHelper;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
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
import org.springframework.core.task.TaskRejectedException;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class SimulateModelAsyncTool implements AiTool {

    private final BoardDataHelper boardDataHelper;
    private final BoardStorageService boardStorageService;
    private final SimulationService simulationService;
    private final ObjectMapper objectMapper;

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
    public String execute(String argsJson) {
        try {
            Long userId = UserContextHolder.getUserId();
            if (userId == null) {
                return errorJson("User not logged in");
            }

            JsonNode args = objectMapper.readTree(argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
            int steps = Math.max(1, Math.min(100, args.path("steps").asInt(10)));
            boolean isAttack = args.path("isAttack").asBoolean(false);
            int intensity = Math.max(0, Math.min(50, args.path("intensity").asInt(3)));
            boolean enablePrivacy = args.path("enablePrivacy").asBoolean(false);

            List<DeviceVerificationDto> devices = boardDataHelper.getDevicesForVerification(userId);
            List<RuleDto> rules = safeList(boardStorageService.getRules(userId));

            if (devices.isEmpty()) {
                return errorJson("No devices found on the board. Please add devices first.");
            }

            Long taskId = simulationService.createTask(userId, steps);
            try {
                simulationService.simulateAsync(userId, taskId, devices, rules, steps, isAttack, intensity, enablePrivacy);
            } catch (TaskRejectedException e) {
                simulationService.failTaskById(taskId, "Server busy, please try again later");
                return errorJson("Simulation task queue is full. Please retry later.");
            }

            return objectMapper.writeValueAsString(Map.of(
                    "message", "Simulation task started.",
                    "taskId", taskId,
                    "status", "PENDING",
                    "progress", 0,
                    "requestedSteps", steps
            ));
        } catch (Exception e) {
            log.error("simulate_model_async failed", e);
            return errorJson("Failed to start simulation task: " + e.getMessage());
        }
    }

    private <T> List<T> safeList(List<T> list) {
        return list == null ? List.of() : list;
    }

    private String errorJson(String message) {
        try {
            return objectMapper.writeValueAsString(Map.of("error", message));
        } catch (Exception e) {
            return "{\"error\":\"" + message + "\"}";
        }
    }
}
