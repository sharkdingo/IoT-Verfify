package cn.edu.nju.Iot_Verify.component.aitool.node;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.NodeService;
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
import java.util.List;
import java.util.LinkedHashMap;
import java.util.Locale;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class DeleteNodeTool implements AiTool {

    private final NodeService nodeService;
    private final BoardStorageService boardStorageService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "delete_device";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("label", Map.of("type", "string", "description", "Device name (label)."));
        props.put("id", Map.of("type", "string", "description", "Device node ID (optional alternative to label)."));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Delete a device node")
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

            JsonNode args = objectMapper.readTree(argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
            String label = trimToNull(args.path("label").asText(null));
            String id = trimToNull(args.path("id").asText(null));
            String identifier = label != null ? label : id;
            if (identifier == null) {
                return errorJson("Missing device identifier. Provide 'label' or 'id'.",
                        "VALIDATION_ERROR", 400);
            }

            String resolvedLabel = resolveNodeLabel(userId, identifier);
            String targetLabel = resolvedLabel != null ? resolvedLabel : identifier;

            log.info("Executing delete_device, identifier={}, resolvedLabel={}", identifier, targetLabel);
            String raw = nodeService.deleteNode(userId, targetLabel);
            return normalizeResult(raw);
        } catch (BaseException e) {
            log.warn("delete_device business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("delete_device failed", e);
            return errorJson("Delete device failed. Please retry.", "INTERNAL_ERROR", 500);
        }
    }

    private String resolveNodeLabel(Long userId, String identifier) {
        List<DeviceNodeDto> nodes = boardStorageService.getNodes(userId);
        if (nodes == null || nodes.isEmpty()) {
            return null;
        }

        String normalized = identifier.toLowerCase(Locale.ROOT);
        for (DeviceNodeDto node : nodes) {
            if (node == null || node.getLabel() == null) {
                continue;
            }
            if (node.getLabel().toLowerCase(Locale.ROOT).equals(normalized)) {
                return node.getLabel();
            }
        }
        for (DeviceNodeDto node : nodes) {
            if (node == null || node.getId() == null || node.getLabel() == null) {
                continue;
            }
            if (node.getId().toLowerCase(Locale.ROOT).equals(normalized)) {
                return node.getLabel();
            }
        }
        return null;
    }

    private String trimToNull(String value) {
        if (value == null) {
            return null;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }

    private String normalizeResult(String raw) {
        if (raw == null || raw.isBlank()) {
            return AiToolResponseHelper.success(objectMapper, "Device delete operation completed.");
        }
        try {
            JsonNode root = objectMapper.readTree(raw);
            if (root.isObject()) {
                return raw;
            }
        } catch (Exception ignore) {
        }
        Map<String, Object> body = new LinkedHashMap<>();
        body.put("message", raw);
        return AiToolResponseHelper.success(objectMapper, body, raw);
    }

    private String errorJson(String message, String errorCode, int status) {
        return AiToolResponseHelper.error(objectMapper, message, errorCode, status);
    }
}
