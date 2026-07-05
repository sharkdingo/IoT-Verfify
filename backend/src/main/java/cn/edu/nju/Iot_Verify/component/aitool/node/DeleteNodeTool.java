package cn.edu.nju.Iot_Verify.component.aitool.node;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.NodeService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
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
public class DeleteNodeTool extends AbstractAiTool {

    private final NodeService nodeService;
    private final BoardStorageService boardStorageService;

    public DeleteNodeTool(NodeService nodeService, BoardStorageService boardStorageService,
                          ObjectMapper objectMapper) {
        super(objectMapper);
        this.nodeService = nodeService;
        this.boardStorageService = boardStorageService;
    }

    @Override
    public String getName() {
        return "delete_device";
    }

    @Override
    public LlmToolSpec getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("identifier", Map.of(
                "type", "string",
                "description", "Preferred device identifier. Use either the device label or node id."
        ));
        props.put("label", Map.of(
                "type", "string",
                "description", "Device label. Backward-compatible alternative to identifier."
        ));
        props.put("id", Map.of(
                "type", "string",
                "description", "Device node id. Backward-compatible alternative to identifier."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return LlmToolSpec.of(getName(),
                "Delete a device node. Provide one of: identifier, label, or id.",
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
            String identifier = trimToNull(args.path("identifier").asText(null));
            String label = trimToNull(args.path("label").asText(null));
            String id = trimToNull(args.path("id").asText(null));
            if (identifier == null) {
                identifier = label != null ? label : id;
            }
            if (identifier == null) {
                return errorJson("Missing device identifier. Provide 'identifier', 'label', or 'id'.",
                        "VALIDATION_ERROR", 400);
            }

            String resolvedLabel = resolveNodeLabel(userId, identifier);
            String targetLabel = resolvedLabel != null ? resolvedLabel : identifier;

            log.info("Executing delete_device, identifier={}, resolvedLabel={}", identifier, targetLabel);
            String raw = nodeService.deleteNode(userId, targetLabel);
            return normalizeResult(raw);
        } catch (ServiceUnavailableException e) {
            log.warn("delete_device busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
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
}
