package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.component.aitool.BoardDataHelper;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.VerificationService;
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
public class VerifyModelAsyncTool implements AiTool {

    private final BoardDataHelper boardDataHelper;
    private final BoardStorageService boardStorageService;
    private final VerificationService verificationService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "verify_model_async";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new LinkedHashMap<>();
        props.put("isAttack", Map.of("type", "boolean", "description", "Enable attack mode. Default false."));
        props.put("intensity", Map.of("type", "integer", "description", "Attack intensity (0-50). Default 3."));
        props.put("enablePrivacy", Map.of("type", "boolean", "description", "Enable privacy dimension modeling. Default false."));

        FunctionParameterSchema schema = new FunctionParameterSchema("object", props, Collections.emptyList());

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Start an async NuSMV verification task. Returns taskId for later polling.")
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
            boolean isAttack = args.path("isAttack").asBoolean(false);
            int intensity = Math.max(0, Math.min(50, args.path("intensity").asInt(3)));
            boolean enablePrivacy = args.path("enablePrivacy").asBoolean(false);

            List<DeviceVerificationDto> devices = boardDataHelper.getDevicesForVerification(userId);
            List<RuleDto> rules = safeList(boardStorageService.getRules(userId));
            List<SpecificationDto> specs = safeList(boardStorageService.getSpecs(userId));

            if (devices.isEmpty()) {
                return errorJson("No devices found on the board. Please add devices first.");
            }
            if (specs.isEmpty()) {
                return errorJson("No specifications found on the board. Please add at least one specification to verify.");
            }

            Long taskId = verificationService.createTask(userId);
            try {
                verificationService.verifyAsync(userId, taskId, devices, rules, specs, isAttack, intensity, enablePrivacy);
            } catch (TaskRejectedException e) {
                verificationService.failTaskById(taskId, "Server busy, please try again later");
                return errorJson("Verification task queue is full. Please retry later.");
            }

            return objectMapper.writeValueAsString(Map.of(
                    "message", "Verification task started.",
                    "taskId", taskId,
                    "status", "PENDING",
                    "progress", 0
            ));
        } catch (Exception e) {
            log.error("verify_model_async failed", e);
            return errorJson("Failed to start verification task: " + e.getMessage());
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
