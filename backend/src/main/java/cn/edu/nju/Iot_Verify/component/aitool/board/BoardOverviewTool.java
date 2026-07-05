package cn.edu.nju.Iot_Verify.component.aitool.board;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;

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

        return LlmToolSpec.of(getName(), "Get an overview of the current board: devices, edges, rules, and specifications summary.", schema);
    }

    @Override
    protected String doExecute(Long userId, String argsJson) {
        try {
            List<DeviceNodeDto> nodes = safeList(boardStorageService.getNodes(userId));
            List<RuleDto> rules = safeList(boardStorageService.getRules(userId));
            List<SpecificationDto> specs = safeList(boardStorageService.getSpecs(userId));
            List<Map<String, Object>> edgeSummaries = buildRuleDerivedEdgeSummaries(nodes, rules);

            Map<String, Object> overview = new LinkedHashMap<>();
            overview.put("deviceCount", nodes.size());
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
                return d;
            }).toList();
            overview.put("devices", deviceSummaries);

            overview.put("edges", edgeSummaries);

            List<Map<String, Object>> ruleSummaries = rules.stream()
                    .filter(Objects::nonNull)
                    .map(r -> {
                Map<String, Object> rs = new LinkedHashMap<>();
                rs.put("id", r.getId());

                List<RuleDto.Condition> conditions = r.getConditions() == null ? List.of() : r.getConditions();
                String condStr = conditions.stream()
                        .filter(Objects::nonNull)
                        .map(c -> safe(c.getDeviceName()) + "." + safe(c.getAttribute())
                                + (c.getRelation() != null ? c.getRelation() : "=")
                                + (c.getValue() != null ? c.getValue() : ""))
                        .collect(Collectors.joining(" AND "));
                rs.put("condition", condStr);

                RuleDto.Command command = r.getCommand();
                if (command != null) {
                    rs.put("action", safe(command.getDeviceName()) + "." + safe(command.getAction()));
                } else {
                    rs.put("action", "");
                }
                return rs;
            }).toList();
            overview.put("rules", ruleSummaries);

            List<Map<String, Object>> specSummaries = specs.stream()
                    .filter(Objects::nonNull)
                    .map(s -> {
                Map<String, Object> ss = new LinkedHashMap<>();
                ss.put("id", s.getId());
                ss.put("label", s.getTemplateLabel());
                ss.put("thenConditionCount", s.getThenConditions() != null ? s.getThenConditions().size() : 0);
                ss.put("ifConditionCount", s.getIfConditions() != null ? s.getIfConditions().size() : 0);
                ss.put("aConditionCount", s.getAConditions() != null ? s.getAConditions().size() : 0);
                return ss;
            }).toList();
            overview.put("specs", specSummaries);

            return objectMapper.writeValueAsString(overview);
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

    private List<Map<String, Object>> buildRuleDerivedEdgeSummaries(List<DeviceNodeDto> nodes,
                                                                    List<RuleDto> rules) {
        Map<String, BoardNodeRef> nodeRefs = indexNodeRefs(nodes);
        List<Map<String, Object>> summaries = new ArrayList<>();

        for (int ruleIndex = 0; ruleIndex < rules.size(); ruleIndex++) {
            RuleDto rule = rules.get(ruleIndex);
            if (rule == null || rule.getCommand() == null || !hasText(rule.getCommand().getDeviceName())) {
                continue;
            }

            RuleDto.Command command = rule.getCommand();
            BoardNodeRef target = resolveNodeRef(command.getDeviceName(), nodeRefs);
            List<RuleDto.Condition> conditions = rule.getConditions() == null ? List.of() : rule.getConditions();

            for (int conditionIndex = 0; conditionIndex < conditions.size(); conditionIndex++) {
                RuleDto.Condition condition = conditions.get(conditionIndex);
                if (condition == null || !hasText(condition.getDeviceName())) {
                    continue;
                }

                BoardNodeRef source = resolveNodeRef(condition.getDeviceName(), nodeRefs);
                Map<String, Object> summary = new LinkedHashMap<>();
                summary.put("id", derivedEdgeId(rule, ruleIndex, conditionIndex));
                summary.put("from", source.id());
                summary.put("to", target.id());
                summary.put("fromLabel", source.label());
                summary.put("toLabel", target.label());
                summary.put("ruleId", rule.getId());
                summary.put("conditionIndex", conditionIndex);
                summary.put("sourceAttribute", safe(condition.getAttribute()));
                summary.put("relation", condition.getRelation() != null ? condition.getRelation() : "=");
                summary.put("value", safe(condition.getValue()));
                summary.put("targetAction", safe(command.getAction()));
                summaries.add(summary);
            }
        }

        return summaries;
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
            if (hasText(node.getLabel())) {
                refs.putIfAbsent(node.getLabel(), ref);
            }
        }
        return refs;
    }

    private BoardNodeRef resolveNodeRef(String rawRef, Map<String, BoardNodeRef> refs) {
        String ref = safe(rawRef);
        return refs.getOrDefault(ref, new BoardNodeRef(ref, ref));
    }

    private String derivedEdgeId(RuleDto rule, int ruleIndex, int conditionIndex) {
        String rulePart = rule.getId() != null ? String.valueOf(rule.getId()) : "index_" + ruleIndex;
        return "rule_" + rulePart + "_condition_" + conditionIndex;
    }

    private boolean hasText(String value) {
        return value != null && !value.isBlank();
    }

    private record BoardNodeRef(String id, String label) {
    }
}
