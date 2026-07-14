package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.component.ai.PromptCompletionService;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * AI-assisted rule similarity analysis.
 *
 * <p>This tool is intentionally separate from {@link CheckDuplicateRuleTool}. Rule creation uses
 * deterministic duplicate checks, while this tool preserves the slower LLM semantic analysis as an
 * explicit user action.
 */
@Slf4j
@Component
public class CheckRuleSimilarityTool extends AbstractAiTool {

    private final BoardStorageService boardStorageService;
    private final PromptCompletionService promptCompletionService;

    private static final double TEMPERATURE = 0.3;
    private static final int MAX_TOKENS = 2000;

    private static final String SYSTEM_PROMPT = """
你是智能物联网(IoT)规则相似性分析助手。你的任务是检查用户新添加的规则是否与现有规则存在语义相似、重叠或重复风险。

## 输入信息
- 新添加的规则详情（触发条件、执行动作、targetType、relation、value 等）
- 用户面板上已有的所有规则列表

## 输出要求
请分析新规则与现有规则的关系，返回符合以下JSON格式的结果：

```json
{
  "isSimilar": true或false,
  "isDuplicate": true或false,
  "mostSimilarWith": "最相似的现有规则 ruleRef（如果有）",
  "duplicateWith": "重复的现有规则 ruleRef（如果有）",
  "similarity": 0.0-1.0,
  "reason": "判断理由"
}
```

## 相似性判定标准
1. **完全重复**: 触发条件和执行动作完全相同，isDuplicate=true
2. **高度相似**: 触发条件和执行动作几乎相同，仅参数略有不同，isSimilar=true
3. **包含关系**: 新规则是现有规则的子集或超集，isSimilar=true
4. **低相似**: 触发条件或执行动作有明显不同，isSimilar=false

## 重要约束
- 必须准确匹配设备的实际变量名、模式名、状态名和API名称
- 必须区分 targetType=api、variable、mode、state；api 条件没有 relation/value
- 如果发现重复，duplicateWith 必须是输入中的重复规则 ruleRef
- 如果 isDuplicate=true，isSimilar 也必须为 true
- 如果只是相似但不重复，mostSimilarWith 必须是输入中的最相似规则 ruleRef，duplicateWith 可以为 null
- 考虑规则的语义相似性，不仅是字面匹配
- 如果没有现有规则，返回 isSimilar=false 且 isDuplicate=false
""";

    public CheckRuleSimilarityTool(BoardStorageService boardStorageService,
                                   PromptCompletionService promptCompletionService,
                                   ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardStorageService = boardStorageService;
        this.promptCompletionService = promptCompletionService;
    }

    @Override
    public String getName() {
        return "check_rule_similarity";
    }

    @Override
    public LlmToolSpec getDefinition() {
        Map<String, Object> props = new LinkedHashMap<>();
        props.put("newRule", RuleCandidateArgument.schema());

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, List.of("newRule")
        );

        return LlmToolSpec.of(getName(),
                "Use AI to analyze whether a new typed rule is semantically similar to existing board rules. " +
                        "This is an explicit user-triggered check and may call the configured LLM.",
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

            requireOnlyFields(args, "arguments", Set.of("newRule"));

            JsonNode newRuleNode = args.path("newRule");
            RuleDto newRule;
            try {
                newRule = RuleCandidateArgument.parse(newRuleNode);
            } catch (RuleCandidateArgument.ValidationException e) {
                return errorJson(e.getMessage(), "VALIDATION_ERROR", 400);
            }

            List<RuleDto> existingRules = safeList(boardStorageService.getRules(userId));
            log.debug("AI rule similarity request: userId={}, existingRules={}", userId, existingRules.size());

            if (existingRules.isEmpty()) {
                return noExistingRulesJson();
            }

            Map<String, RuleDto> ruleReferences = ruleReferences(existingRules);
            String aiResponse = analyzeSimilarityWithAI(
                    buildRuleInfoJson(newRule, "new-rule"),
                    buildRulesListJson(ruleReferences));
            log.debug("AI rule similarity response length: {} chars", aiResponse.length());

            return parseAiResponse(aiResponse, ruleReferences);
        } catch (ArgValidationException e) {
            return e.getErrorResponse();
        } catch (ServiceUnavailableException e) {
            log.warn("check_rule_similarity busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("check_rule_similarity business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("check_rule_similarity failed", e);
            return errorJson("Failed to check rule similarity.", "INTERNAL_ERROR", 500);
        }
    }

    private String noExistingRulesJson() throws Exception {
        Map<String, Object> body = new LinkedHashMap<>();
        body.put("isSimilar", false);
        body.put("isDuplicate", false);
        body.put("requiresReview", false);
        body.put("matchedRule", null);
        body.put("similarity", 0.0);
        body.put("reasonCode", "NO_EXISTING_RULES");
        body.put("reason", "no existing rules");
        body.put("message", "No existing rules to compare. This is the first rule.");
        return objectMapper.writeValueAsString(body);
    }

    private String buildRuleInfoJson(RuleDto rule, String prefix) {
        try {
            return objectMapper.writeValueAsString(buildRuleInfoMap(rule, prefix));
        } catch (Exception e) {
            log.error("Failed to build rule similarity JSON", e);
            throw new IllegalStateException("Could not serialize the candidate rule for similarity analysis", e);
        }
    }

    private String buildRulesListJson(Map<String, RuleDto> ruleReferences) {
        try {
            List<Map<String, Object>> rulesList = new ArrayList<>();
            for (Map.Entry<String, RuleDto> entry : ruleReferences.entrySet()) {
                rulesList.add(buildRuleInfoMap(entry.getValue(), entry.getKey()));
            }
            return objectMapper.writeValueAsString(rulesList);
        } catch (Exception e) {
            log.error("Failed to build existing rules similarity JSON", e);
            throw new IllegalStateException("Could not serialize existing rules for similarity analysis", e);
        }
    }

    private Map<String, Object> buildRuleInfoMap(RuleDto rule, String prefix) {
        Map<String, Object> ruleMap = new LinkedHashMap<>();
        ruleMap.put("ruleRef", prefix);

        if (rule.getConditions() != null && !rule.getConditions().isEmpty()) {
            List<Map<String, Object>> conditions = new ArrayList<>();
            for (RuleDto.Condition cond : rule.getConditions()) {
                Map<String, Object> condMap = new LinkedHashMap<>();
                condMap.put("deviceName", cond.getDeviceName());
                condMap.put("targetType", cond.getTargetType());
                condMap.put("attribute", cond.getAttribute());
                condMap.put("relation", cond.getRelation());
                condMap.put("value", cond.getValue());
                conditions.add(condMap);
            }
            ruleMap.put("conditions", conditions);
        } else {
            ruleMap.put("conditions", Collections.emptyList());
        }

        if (rule.getCommand() != null) {
            Map<String, Object> commandMap = new LinkedHashMap<>();
            commandMap.put("deviceName", rule.getCommand().getDeviceName());
            commandMap.put("action", rule.getCommand().getAction());
            commandMap.put("contentDevice", rule.getCommand().getContentDevice());
            commandMap.put("content", rule.getCommand().getContent());
            ruleMap.put("command", commandMap);
        }

        return ruleMap;
    }

    private String analyzeSimilarityWithAI(String newRuleInfo, String existingRulesInfo) {
        String userPrompt = """
请检查新添加的规则是否与现有规则存在语义相似、重叠或重复风险。

## 新添加的规则
%s

## 现有规则列表
%s

请直接返回JSON格式的检查结果，不要包含其他文字。
""".formatted(newRuleInfo, existingRulesInfo);

        String content = promptCompletionService.complete(SYSTEM_PROMPT, userPrompt, TEMPERATURE, MAX_TOKENS);
        if (content == null || content.isBlank()) {
            log.warn("AI returned empty content for rule similarity check");
            return "";
        }
        return content;
    }

    private String parseAiResponse(String aiResponse, Map<String, RuleDto> ruleReferences) {
        try {
            JsonNode root = objectMapper.readTree(cleanFence(aiResponse));
            if (root == null || !root.isObject()
                    || !root.path("isSimilar").isBoolean()
                    || !root.path("isDuplicate").isBoolean()
                    || !root.path("similarity").isNumber()) {
                throw new IllegalArgumentException(
                        "AI similarity response must contain boolean isSimilar/isDuplicate and numeric similarity");
            }

            double similarity = root.path("similarity").asDouble();
            boolean isDuplicate = root.path("isDuplicate").asBoolean();
            boolean isSimilar = root.path("isSimilar").asBoolean();
            if (!Double.isFinite(similarity) || similarity < 0.0 || similarity > 1.0) {
                throw new IllegalArgumentException("AI similarity score must be between 0 and 1");
            }
            if (isDuplicate && !isSimilar) {
                throw new IllegalArgumentException("An AI duplicate result must also be marked similar");
            }
            String duplicateWith = textOrNull(root.path("duplicateWith"));
            String mostSimilarWith = textOrNull(root.path("mostSimilarWith"));
            if (mostSimilarWith == null) {
                mostSimilarWith = duplicateWith;
            }

            RuleDto duplicateRule = referencedRule(duplicateWith, ruleReferences);
            RuleDto mostSimilarRule = referencedRule(mostSimilarWith, ruleReferences);
            RuleDto matchedRule = duplicateRule != null ? duplicateRule : mostSimilarRule;

            Map<String, Object> result = new LinkedHashMap<>();
            boolean requiresReview = isDuplicate || isSimilar || similarity >= 0.8;
            String reasonCode = isDuplicate
                    ? "AI_DUPLICATE"
                    : isSimilar
                    ? "AI_SIMILAR"
                    : similarity >= 0.8
                    ? "AI_HIGH_SCORE_REVIEW"
                    : "AI_NO_SIGNIFICANT_SIMILARITY";
            result.put("isSimilar", isSimilar);
            result.put("isDuplicate", isDuplicate);
            result.put("requiresReview", requiresReview);
            result.put("matchedRule", matchedRule == null ? null : displayRule(matchedRule));
            result.put("similarity", similarity);
            result.put("reasonCode", reasonCode);
            result.put("reason", root.path("reason").asText(""));
            result.put("message", isDuplicate
                    ? matchedRule == null
                    ? "AI found a possible duplicate but could not identify the referenced existing rule."
                    : "AI found a duplicate rule: " + displayRule(matchedRule)
                    : isSimilar
                    ? matchedRule == null
                    ? "AI found a possible similar rule but could not identify the referenced existing rule."
                    : "AI found a similar rule: " + displayRule(matchedRule)
                    : "AI found no obvious similar rule; this is not a conflict-free proof.");
            return objectMapper.writeValueAsString(result);
        } catch (Exception e) {
            log.error("Failed to parse AI rule similarity response", e);
            return errorJson(
                    "Failed to parse AI similarity result. Please try again.",
                    "AI_RESPONSE_INVALID",
                    502,
                    Map.of("phase", "response_parse"));
        }
    }

    private String cleanFence(String aiResponse) {
        String cleaned = aiResponse == null ? "" : aiResponse.trim();
        if (cleaned.startsWith("```")) {
            int firstNewline = cleaned.indexOf('\n');
            if (firstNewline > 0) {
                cleaned = cleaned.substring(firstNewline).trim();
            }
        }
        if (cleaned.endsWith("```")) {
            cleaned = cleaned.substring(0, cleaned.lastIndexOf("```")).trim();
        }
        return cleaned;
    }

    private String textOrNull(JsonNode node) {
        if (node == null || node.isMissingNode() || node.isNull()) {
            return null;
        }
        String text = node.asText(null);
        return text == null || text.isBlank() ? null : text.trim();
    }

    private Map<String, RuleDto> ruleReferences(List<RuleDto> existingRules) {
        Map<String, RuleDto> references = new LinkedHashMap<>();
        int index = 1;
        for (RuleDto rule : existingRules) {
            references.put("candidate-" + index++, rule);
        }
        return references;
    }

    private RuleDto referencedRule(String reference, Map<String, RuleDto> ruleReferences) {
        return reference == null || ruleReferences == null ? null : ruleReferences.get(reference);
    }

    private String displayRule(RuleDto rule) {
        if (rule != null && rule.getRuleString() != null && !rule.getRuleString().isBlank()) {
            return rule.getRuleString();
        }
        if (rule == null || rule.getCommand() == null) {
            return "?";
        }
        return rule.getCommand().getDeviceName() + "." + rule.getCommand().getAction();
    }
}
