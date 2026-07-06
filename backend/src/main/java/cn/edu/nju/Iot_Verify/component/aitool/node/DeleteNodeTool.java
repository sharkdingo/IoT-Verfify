package cn.edu.nju.Iot_Verify.component.aitool.node;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.NodeService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;

@Slf4j
@Component
public class DeleteNodeTool extends AbstractAiTool {

    private final BoardStorageService boardStorageService;

    public DeleteNodeTool(NodeService nodeService, BoardStorageService boardStorageService,
                          ObjectMapper objectMapper) {
        super(objectMapper);
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

            List<DeviceNodeDto> nodes = safeList(boardStorageService.getNodes(userId));
            DeviceNodeDto targetNode = resolveNode(nodes, identifier);
            if (targetNode == null) {
                return errorJson("Device not found for deletion: '" + identifier + "'.",
                        "NOT_FOUND", 404);
            }

            log.info("Executing delete_device, identifier={}, resolvedId={}, resolvedLabel={}",
                    identifier, targetNode.getId(), targetNode.getLabel());

            DeletePlan plan = buildDeletePlan(userId, nodes, targetNode);
            boardStorageService.saveBoardBatch(userId,
                    new BoardBatchDto(plan.nodes(), plan.rules(), plan.specs()));

            return successJson(Map.of(
                    "message", "Device deleted successfully.",
                    "deletedDeviceId", targetNode.getId(),
                    "deletedDeviceLabel", targetNode.getLabel(),
                    "removedRules", plan.removedRuleCount(),
                    "removedSpecs", plan.removedSpecCount()
            ), "Device deleted successfully.");
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

    private DeviceNodeDto resolveNode(List<DeviceNodeDto> nodes, String identifier) {
        String normalized = identifier.toLowerCase(Locale.ROOT);
        for (DeviceNodeDto node : nodes) {
            if (node == null || node.getLabel() == null) {
                continue;
            }
            if (node.getLabel().toLowerCase(Locale.ROOT).equals(normalized)) {
                return node;
            }
        }
        for (DeviceNodeDto node : nodes) {
            if (node == null || node.getId() == null) {
                continue;
            }
            if (node.getId().toLowerCase(Locale.ROOT).equals(normalized)) {
                return node;
            }
        }
        return null;
    }

    private DeletePlan buildDeletePlan(Long userId, List<DeviceNodeDto> nodes, DeviceNodeDto targetNode) {
        List<DeviceNodeDto> nextNodes = nodes.stream()
                .filter(node -> !isDeletedNode(node, targetNode))
                .toList();

        List<RuleDto> rules = safeList(boardStorageService.getRules(userId));
        List<RuleDto> nextRules = new ArrayList<>();
        int removedRules = 0;
        for (RuleDto rule : rules) {
            if (isRuleRelatedToNode(rule, targetNode)) {
                removedRules++;
            } else {
                nextRules.add(rule);
            }
        }

        List<SpecificationDto> specs = safeList(boardStorageService.getSpecs(userId));
        List<SpecificationDto> nextSpecs = new ArrayList<>();
        int removedSpecs = 0;
        for (SpecificationDto spec : specs) {
            if (isSpecRelatedToNode(spec, targetNode)) {
                removedSpecs++;
            } else {
                nextSpecs.add(spec);
            }
        }

        return new DeletePlan(nextNodes, nextRules, nextSpecs, removedRules, removedSpecs);
    }

    private boolean isDeletedNode(DeviceNodeDto node, DeviceNodeDto targetNode) {
        if (node == null) {
            return false;
        }
        String nodeId = trimToNull(node.getId());
        String targetId = trimToNull(targetNode.getId());
        if (targetId == null || nodeId == null) {
            return false;
        }
        return targetId.equals(nodeId)
                || (nodeId.startsWith(targetId + "_")
                && node.getTemplateName() != null
                && node.getTemplateName().startsWith("variable_"));
    }

    private boolean isRuleRelatedToNode(RuleDto rule, DeviceNodeDto targetNode) {
        if (rule == null) {
            return false;
        }
        if (rule.getCommand() != null
                && (matchesNode(rule.getCommand().getDeviceName(), targetNode)
                || matchesNode(rule.getCommand().getContentDevice(), targetNode))) {
            return true;
        }
        for (RuleDto.Condition condition : safeList(rule.getConditions())) {
            if (condition != null && matchesNode(condition.getDeviceName(), targetNode)) {
                return true;
            }
        }
        return false;
    }

    private boolean isSpecRelatedToNode(SpecificationDto spec, DeviceNodeDto targetNode) {
        if (spec == null) {
            return false;
        }
        for (SpecConditionDto condition : safeList(spec.getAConditions())) {
            if (conditionMatchesNode(condition, targetNode)) {
                return true;
            }
        }
        for (SpecConditionDto condition : safeList(spec.getIfConditions())) {
            if (conditionMatchesNode(condition, targetNode)) {
                return true;
            }
        }
        for (SpecConditionDto condition : safeList(spec.getThenConditions())) {
            if (conditionMatchesNode(condition, targetNode)) {
                return true;
            }
        }
        for (SpecificationDto.DeviceRefDto device : safeList(spec.getDevices())) {
            if (device != null
                    && (matchesNode(device.getDeviceId(), targetNode)
                    || matchesNode(device.getDeviceLabel(), targetNode))) {
                return true;
            }
        }
        return false;
    }

    private boolean conditionMatchesNode(SpecConditionDto condition, DeviceNodeDto targetNode) {
        return condition != null
                && (matchesNode(condition.getDeviceId(), targetNode)
                || matchesNode(condition.getDeviceLabel(), targetNode));
    }

    private boolean matchesNode(String value, DeviceNodeDto targetNode) {
        String normalized = trimToNull(value);
        if (normalized == null || targetNode == null) {
            return false;
        }
        return normalized.equals(targetNode.getId()) || normalized.equals(targetNode.getLabel());
    }

    private record DeletePlan(List<DeviceNodeDto> nodes,
                              List<RuleDto> rules,
                              List<SpecificationDto> specs,
                              int removedRuleCount,
                              int removedSpecCount) {
    }
}
