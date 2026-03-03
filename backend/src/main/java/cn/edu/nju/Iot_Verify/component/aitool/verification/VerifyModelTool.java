package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.component.aitool.BoardDataHelper;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
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
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class VerifyModelTool implements AiTool {

    private final BoardDataHelper boardDataHelper;
    private final BoardStorageService boardStorageService;
    private final VerificationService verificationService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "verify_model";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("isAttack", Map.of(
                "type", "boolean",
                "description", "Enable attack mode simulation. Default false."
        ));
        props.put("intensity", Map.of(
                "type", "integer",
                "description", "Attack intensity (0-50). Only effective when isAttack=true. Default 3."
        ));
        props.put("enablePrivacy", Map.of(
                "type", "boolean",
                "description", "Enable privacy dimension modeling. Only needed when specs contain privacy conditions. Default false."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Run NuSMV formal verification on the current board. " +
                                "Automatically reads all devices, rules, and specifications from the board. " +
                                "Returns whether the model is safe and details of any property violations. " +
                                "Requires at least one device and one specification on the board.")
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
            boolean isAttack = args.path("isAttack").asBoolean(false);
            int intensity = args.path("intensity").asInt(3);
            boolean enablePrivacy = args.path("enablePrivacy").asBoolean(false);
            intensity = Math.max(0, Math.min(50, intensity));

            // Load board data directly from current workspace state.
            List<DeviceVerificationDto> devices = boardDataHelper.getDevicesForVerification(userId);
            List<RuleDto> rules = safeList(boardStorageService.getRules(userId));
            List<SpecificationDto> specs = safeList(boardStorageService.getSpecs(userId));

            if (devices.isEmpty()) {
                return errorJson("No devices found on the board. Please add devices first.",
                        "VALIDATION_ERROR", 400);
            }
            if (specs.isEmpty()) {
                return errorJson("No specifications found on the board. Please add at least one specification to verify.",
                        "VALIDATION_ERROR", 400);
            }

            log.info("Executing verify_model: {} devices, {} rules, {} specs, attack={}, intensity={}, privacy={}",
                    devices.size(), rules.size(), specs.size(), isAttack, intensity, enablePrivacy);

            VerificationResultDto result = verificationService.verify(
                    userId, devices, rules, specs, isAttack, intensity, enablePrivacy);

            // Build a compact summary for chat output.
            Map<String, Object> summary = new LinkedHashMap<>();
            summary.put("safe", result.isSafe());
            summary.put("specsChecked", specs.size());
            summary.put("specResults", result.getSpecResults());

            if (!result.isSafe() && result.getTraces() != null) {
                summary.put("violationCount", result.getTraces().size());
                List<Map<String, Object>> traceSummaries = new ArrayList<>();
                for (TraceDto trace : result.getTraces()) {
                    Map<String, Object> ts = new LinkedHashMap<>();
                    ts.put("traceId", trace.getId());
                    ts.put("violatedSpecId", trace.getViolatedSpecId());
                    ts.put("stateCount", trace.getStates() != null ? trace.getStates().size() : 0);
                    traceSummaries.add(ts);
                }
                summary.put("traces", traceSummaries);
            }

            if (result.getCheckLogs() != null && !result.getCheckLogs().isEmpty()) {
                summary.put("checkLogs", result.getCheckLogs());
            }

            return successJson(summary, "Verification completed.");
        } catch (ServiceUnavailableException e) {
            log.warn("verify_model busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (SmvGenerationException e) {
            log.warn("verify_model generation failed [{}]: {}", e.getErrorCategory(), e.getMessage());
            return errorJson(e.getMessage(),
                    "SMV_GENERATION_ERROR",
                    500,
                    Map.of("errorCategory", e.getErrorCategory()));
        } catch (BaseException e) {
            log.warn("verify_model business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("verify_model failed", e);
            return errorJson("Verification failed.", "INTERNAL_ERROR", 500);
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
