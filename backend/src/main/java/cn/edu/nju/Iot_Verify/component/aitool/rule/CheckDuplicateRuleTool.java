package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import cn.edu.nju.Iot_Verify.util.RuleSemanticSignature;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

/**
 * 规则重复检查工具
 * 当用户添加一条规则后，使用确定性规则签名检查该规则是否与现有规则重复。
 */
@Slf4j
@Component
public class CheckDuplicateRuleTool extends AbstractAiTool {

    private final BoardStorageService boardStorageService;

    public CheckDuplicateRuleTool(BoardStorageService boardStorageService,
                                  ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardStorageService = boardStorageService;
    }

    @Override
    public String getName() {
        return "check_duplicate_rule";
    }

    @Override
    public LlmToolSpec getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("newRule", RuleCandidateArgument.schema());

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, List.of("newRule")
        );

        return LlmToolSpec.of(getName(),
                "Check if a new rule is duplicate with existing rules on the board. " +
                        "Uses deterministic typed trigger/action signatures so rule creation is not blocked by LLM latency.",
                schema);
    }

    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }

            requireOnlyFields(args, "arguments", Set.of("newRule"));

            JsonNode newRuleNode = args.path("newRule");
            RuleDto newRule;
            try {
                newRule = RuleCandidateArgument.parse(newRuleNode);
            } catch (RuleCandidateArgument.ValidationException e) {
                return errorJson(e.getMessage(), "VALIDATION_ERROR", 400);
            }

            // 获取现有规则
            List<RuleDto> existingRules = safeList(boardStorageService.getRules(userId));

            log.debug("Duplicate rule check request: userId={}, existingRules={}", userId, existingRules.size());

            if (existingRules.isEmpty()) {
                // 没有现有规则，直接返回不重复。
                // 注意：不能用 Map.of(...)，因为它禁止 null 值，会在 "matchedRule"=null 时抛 NPE，
                // 导致库中第一条规则做重复检查时被 catch(Exception) 转成 500 而非 {isDuplicate:false}。
                Map<String, Object> body = new HashMap<>();
                body.put("isDuplicate", false);
                body.put("requiresReview", false);
                body.put("matchedRule", null);
                body.put("similarity", 0.0);
                body.put("matchType", "none");
                body.put("reasonCode", "NO_EXISTING_RULES");
                body.put("reason", "no existing rules");
                body.put("message", "No existing rules to compare. This is the first rule.");
                return objectMapper.writeValueAsString(body);
            }

            String result = objectMapper.writeValueAsString(checkDuplicateDeterministically(newRule, existingRules));
            log.debug("Duplicate rule check result length: {} chars", result.length());
            return result;

        } catch (ArgValidationException e) {
            return e.getErrorResponse();
        } catch (ServiceUnavailableException e) {
            log.warn("check_duplicate_rule busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("check_duplicate_rule business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("check_duplicate_rule failed", e);
            return errorJson("Failed to check duplicate rule.", "INTERNAL_ERROR", 500);
        }
    }

    private Map<String, Object> checkDuplicateDeterministically(RuleDto newRule, List<RuleDto> existingRules) {
        RuleSemanticSignature.Signature newSignature = RuleSemanticSignature.from(newRule);
        DuplicateCandidate best = DuplicateCandidate.none();

        for (RuleDto existingRule : existingRules) {
            if (newRule.getId() != null && newRule.getId().equals(existingRule.getId())) {
                continue;
            }
            DuplicateCandidate candidate = compare(
                    newSignature, RuleSemanticSignature.from(existingRule), existingRule);
            if (candidate.similarity > best.similarity) {
                best = candidate;
            }
        }

        Map<String, Object> result = new LinkedHashMap<>();
        result.put("isDuplicate", best.isDuplicate);
        result.put("requiresReview", best.requiresReview);
        result.put("matchedRule", best.matchedRule);
        result.put("similarity", best.similarity);
        result.put("matchType", best.matchType);
        result.put("reasonCode", best.reasonCode);
        result.put("reason", best.reason);
        result.put("message", best.isDuplicate
                ? "This rule is identical to: " + best.matchedRule
                : best.requiresReview
                    ? "This rule may overlap with: " + best.matchedRule
                    : "No obvious duplicate rule found; this is not a conflict-free proof.");
        return result;
    }

    private DuplicateCandidate compare(RuleSemanticSignature.Signature candidate,
                                       RuleSemanticSignature.Signature existing,
                                       RuleDto existingRule) {
        if (!candidate.commandKey().equals(existing.commandKey())) {
            return DuplicateCandidate.none();
        }

        String matchedRule = displayRule(existingRule);
        if (candidate.conditionKeys().equals(existing.conditionKeys())) {
            return new DuplicateCandidate(true, true, matchedRule, 1.0, "exact",
                    "EXACT_MATCH",
                    "same trigger conditions and same action");
        }

        if (!candidate.conditionKeys().isEmpty() && !existing.conditionKeys().isEmpty()) {
            if (existing.conditionKeys().containsAll(candidate.conditionKeys())
                    || candidate.conditionKeys().containsAll(existing.conditionKeys())) {
                double ratio = Math.min(candidate.conditionKeys().size(), existing.conditionKeys().size())
                        / (double) Math.max(candidate.conditionKeys().size(), existing.conditionKeys().size());
                return new DuplicateCandidate(false, true, matchedRule, Math.max(0.85, ratio), "contains",
                        "TRIGGER_SET_CONTAINS_OTHER",
                        "same action and one trigger set contains the other");
            }
        }

        if (candidate.conditionShapeKeys().equals(existing.conditionShapeKeys())) {
            return new DuplicateCandidate(false, true, matchedRule, 0.82, "same-shape",
                    "SAME_TRIGGER_SHAPE_DIFFERENT_VALUES",
                    "same action and trigger structure with different parameter values");
        }

        Set<String> intersection = new HashSet<>(candidate.conditionShapeKeys());
        intersection.retainAll(existing.conditionShapeKeys());
        if (!intersection.isEmpty()) {
            double similarity = 0.45 + 0.3 * intersection.size()
                    / Math.max(candidate.conditionShapeKeys().size(), existing.conditionShapeKeys().size());
            return new DuplicateCandidate(false, false, null, similarity, "partial-shape",
                    "PARTIAL_TRIGGER_OVERLAP",
                    "same action with partially overlapping trigger structure");
        }

        return DuplicateCandidate.none();
    }

    private record DuplicateCandidate(
            boolean isDuplicate,
            boolean requiresReview,
            String matchedRule,
            double similarity,
            String matchType,
            String reasonCode,
            String reason
    ) {
        static DuplicateCandidate none() {
            return new DuplicateCandidate(false, false, null, 0.0, "none",
                    "NO_MATCHING_SIGNATURE", "no matching rule signature");
        }
    }

    private String displayRule(RuleDto rule) {
        if (rule != null && rule.getRuleString() != null && !rule.getRuleString().isBlank()) {
            return rule.getRuleString();
        }
        if (rule == null || rule.getCommand() == null) {
            return "?";
        }
        String conditions = safeList(rule.getConditions()).stream()
                .filter(java.util.Objects::nonNull)
                .map(condition -> {
                    String base = displayText(condition.getDeviceName()) + "." + displayText(condition.getAttribute());
                    if ("api".equalsIgnoreCase(displayText(condition.getTargetType()))) {
                        return base;
                    }
                    return base + " " + displayText(condition.getRelation()) + " " + displayText(condition.getValue());
                })
                .reduce((left, right) -> left + " & " + right)
                .orElse("?");
        return conditions + " -> " + displayText(rule.getCommand().getDeviceName())
                + "." + displayText(rule.getCommand().getAction());
    }

    private String displayText(String value) {
        return value == null ? "" : value.trim();
    }

}
