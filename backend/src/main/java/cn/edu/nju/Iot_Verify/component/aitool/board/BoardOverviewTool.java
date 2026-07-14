package cn.edu.nju.Iot_Verify.component.aitool.board;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.component.aitool.spec.SpecificationToolPresenter;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import cn.edu.nju.Iot_Verify.util.SpecificationFormulaPreview;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

@Slf4j
@Component
public class BoardOverviewTool extends AbstractAiTool {

    private final BoardStorageService boardStorageService;

    public BoardOverviewTool(BoardStorageService boardStorageService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardStorageService = boardStorageService;
    }

    @Override
    public String getName() {
        return "board_overview";
    }

    @Override
    public LlmToolSpec getDefinition() {
        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", Collections.emptyMap(), Collections.emptyList()
        );

        return LlmToolSpec.of(getName(), "Get an overview of the current board: device runtime values, the shared environment pool, rule-derived edges, rules, and specifications.", schema);
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
            requireOnlyFields(args, "arguments", Collections.emptySet());

            List<DeviceNodeDto> nodes = safeList(boardStorageService.getNodes(userId));
            List<DeviceTemplateDto> templates = safeList(boardStorageService.getDeviceTemplates(userId));
            List<BoardEnvironmentVariableDto> environmentVariables =
                    safeList(boardStorageService.getEnvironmentVariables(userId));
            List<RuleDto> rules = safeList(boardStorageService.getRules(userId));
            List<SpecificationDto> specs = safeList(boardStorageService.getSpecs(userId));
            Map<String, BoardNodeRef> nodeRefs = indexNodeRefs(nodes);
            SpecificationFormulaPreview.Context presentationContext =
                    SpecificationToolPresenter.context(nodes, templates);
            List<Map<String, Object>> edgeSummaries = buildRuleDerivedEdgeSummaries(nodeRefs, rules);

            Map<String, Object> overview = new LinkedHashMap<>();
            overview.put("deviceCount", nodes.size());
            overview.put("environmentVariableCount", environmentVariables.size());
            overview.put("edgeCount", edgeSummaries.size());
            overview.put("ruleCount", rules.size());
            overview.put("specCount", specs.size());

            List<Map<String, Object>> deviceSummaries = nodes.stream()
                    .filter(Objects::nonNull)
                    .map(n -> {
                Map<String, Object> d = new LinkedHashMap<>();
                d.put("id", n.getId());
                d.put("label", n.getLabel());
                d.put("templateName", n.getTemplateName());
                d.put("state", n.getState());
                d.put("currentStateTrust", n.getCurrentStateTrust());
                d.put("currentStatePrivacy", n.getCurrentStatePrivacy());
                d.put("variables", n.getVariables() != null ? n.getVariables() : List.of());
                d.put("privacies", n.getPrivacies() != null ? n.getPrivacies() : List.of());
                return d;
            }).toList();
            overview.put("devices", deviceSummaries);
            overview.put("environmentVariables", environmentVariables);

            overview.put("edges", edgeSummaries);

            List<Map<String, Object>> ruleSummaries = rules.stream()
                    .filter(Objects::nonNull)
                    .map(r -> {
                Map<String, Object> rs = new LinkedHashMap<>();
                List<RuleDto.Condition> conditions = r.getConditions() == null ? List.of() : r.getConditions();
                List<Map<String, Object>> conditionRows = conditions.stream()
                        .filter(Objects::nonNull)
                        .map(condition -> ruleConditionSummary(condition, nodeRefs))
                        .toList();
                rs.put("conditions", conditionRows);

                RuleDto.Command command = r.getCommand();
                Map<String, Object> commandRow = ruleCommandSummary(command, nodeRefs);
                rs.put("command", commandRow);
                rs.put("description", buildRuleDescription(conditionRows, commandRow));
                return rs;
            }).toList();
            overview.put("rules", ruleSummaries);

            List<Map<String, Object>> specSummaries = specs.stream()
                    .filter(Objects::nonNull)
                    .map(s -> {
                Map<String, Object> ss = new LinkedHashMap<>(
                        SpecificationToolPresenter.present(s, presentationContext));
                ss.remove("specId");
                return ss;
            }).toList();
            overview.put("specs", specSummaries);

            return objectMapper.writeValueAsString(overview);
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
        } catch (ServiceUnavailableException e) {
            log.warn("board_overview busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("board_overview business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("board_overview failed", e);
            return errorJson("Failed to get board overview. Please retry.", "INTERNAL_ERROR", 500);
        }
    }

    private String safe(String value) {
        return value == null ? "" : value;
    }

    private List<Map<String, Object>> buildRuleDerivedEdgeSummaries(Map<String, BoardNodeRef> nodeRefs,
                                                                    List<RuleDto> rules) {
        List<Map<String, Object>> summaries = new ArrayList<>();

        for (RuleDto rule : rules) {
            if (rule == null || rule.getCommand() == null || !hasText(rule.getCommand().getDeviceName())) {
                continue;
            }

            RuleDto.Command command = rule.getCommand();
            BoardNodeRef target = resolveNodeRef(command.getDeviceName(), nodeRefs);
            List<RuleDto.Condition> conditions = rule.getConditions() == null ? List.of() : rule.getConditions();

            for (RuleDto.Condition condition : conditions) {
                if (condition == null || !hasText(condition.getDeviceName())) {
                    continue;
                }

                BoardNodeRef source = resolveNodeRef(condition.getDeviceName(), nodeRefs);
                Map<String, Object> summary = new LinkedHashMap<>();
                summary.put("from", source.id());
                summary.put("to", target.id());
                summary.put("fromLabel", source.label());
                summary.put("toLabel", target.label());
                summary.put("ruleDescription", rule.getRuleString());
                summary.put("sourceType", condition.getTargetType());
                summary.put("sourceAttribute", safe(condition.getAttribute()));
                summary.put("relation", condition.getRelation() != null ? condition.getRelation() : "=");
                summary.put("value", safe(condition.getValue()));
                summary.put("targetAction", safe(command.getAction()));
                summaries.add(summary);
            }
        }

        return summaries;
    }

    private Map<String, Object> ruleConditionSummary(RuleDto.Condition condition,
                                                     Map<String, BoardNodeRef> nodeRefs) {
        BoardNodeRef device = resolveNodeRef(condition.getDeviceName(), nodeRefs);
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("deviceId", device.id());
        row.put("deviceLabel", device.label());
        row.put("targetType", condition.getTargetType());
        row.put("attribute", condition.getAttribute());
        row.put("relation", condition.getRelation());
        row.put("value", condition.getValue());
        row.put("summary", conditionText(device.label(), condition.getTargetType(),
                condition.getAttribute(), condition.getRelation(), condition.getValue()));
        return row;
    }

    private Map<String, Object> ruleCommandSummary(RuleDto.Command command,
                                                   Map<String, BoardNodeRef> nodeRefs) {
        Map<String, Object> row = new LinkedHashMap<>();
        if (command == null) {
            row.put("summary", "No command");
            return row;
        }
        BoardNodeRef target = resolveNodeRef(command.getDeviceName(), nodeRefs);
        row.put("deviceId", target.id());
        row.put("deviceLabel", target.label());
        row.put("action", command.getAction());
        String summary = target.label() + "." + safe(command.getAction());
        if (hasText(command.getContentDevice())) {
            BoardNodeRef contentSource = resolveNodeRef(command.getContentDevice(), nodeRefs);
            row.put("contentDeviceId", contentSource.id());
            row.put("contentDeviceLabel", contentSource.label());
            row.put("content", command.getContent());
            summary += " using " + contentSource.label() + "." + safe(command.getContent());
        }
        row.put("summary", summary);
        return row;
    }

    private String conditionText(String deviceLabel, String targetType, String attribute,
                                 String relation, String value) {
        String subject = (hasText(deviceLabel) ? deviceLabel : "Unknown device") + "." + safe(attribute);
        if ("api".equalsIgnoreCase(targetType) && !hasText(relation) && !hasText(value)) {
            return subject + " occurs";
        }
        return subject + (hasText(relation) ? " " + relation : "")
                + (hasText(value) ? " " + value : "");
    }

    private String buildRuleDescription(List<Map<String, Object>> conditions, Map<String, Object> command) {
        String conditionText = conditions.stream()
                .map(row -> safe((String) row.get("summary")))
                .filter(this::hasText)
                .reduce((left, right) -> left + " AND " + right)
                .orElse("No trigger");
        return "IF " + conditionText + " THEN " + safe((String) command.get("summary"));
    }

    private Map<String, BoardNodeRef> indexNodeRefs(List<DeviceNodeDto> nodes) {
        Map<String, BoardNodeRef> refs = new LinkedHashMap<>();
        for (DeviceNodeDto node : nodes) {
            if (node == null) {
                continue;
            }
            BoardNodeRef ref = new BoardNodeRef(safe(node.getId()), safe(node.getLabel()));
            if (hasText(node.getId())) {
                refs.putIfAbsent(node.getId(), ref);
            }
        }
        return refs;
    }

    private BoardNodeRef resolveNodeRef(String rawRef, Map<String, BoardNodeRef> refs) {
        String ref = safe(rawRef);
        return refs.getOrDefault(ref, new BoardNodeRef(ref, "Unknown device"));
    }

    private boolean hasText(String value) {
        return value != null && !value.isBlank();
    }

    private record BoardNodeRef(String id, String label) {
    }
}
