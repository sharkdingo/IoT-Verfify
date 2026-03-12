package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.client.ArkAiClient;
import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.component.aitool.AiToolResponseHelper;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionRequest;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionResult;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessage;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessageRole;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

/**
 * 规则重复检查工具
 * 当用户添加一条规则后，检查该规则是否与现有规则重复
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class CheckDuplicateRuleTool implements AiTool {

    private final BoardStorageService boardStorageService;
    private final ArkAiClient arkAiClient;
    private final ObjectMapper objectMapper;

    private static final String SYSTEM_PROMPT = """
你是智能物联网(IoT)规则重复性检查助手。你的任务是检查用户新添加的规则是否与现有规则重复。

## 输入信息
- 新添加的规则详情（触发条件、执行动作等）
- 用户面板上已有的所有规则列表

## 输出要求
请分析新规则与现有规则的关系，返回符合以下JSON格式的结果：

```json
{
  "isDuplicate": true或false,
  "duplicateWith": "重复的现有规则ID（如果有）",
  "similarity": 0.0-1.0,
  "reason": "判断理由"
}
```

## 重复判定标准
1. **完全相同**: 触发条件和执行动作完全相同
2. **高度相似**: 触发条件和执行动作几乎相同，仅参数略有不同
3. **包含关系**: 新规则是现有规则的子集或超集
4. **不重复**: 触发条件或执行动作有明显不同

## 重要约束
- 必须准确匹配设备的实际变量名和API名称
- 如果发现重复，返回重复的规则ID和相似度
- 考虑规则的语义相似性，不仅是字面匹配
- 如果没有现有规则，返回isDuplicate为false
""";

    @Override
    public String getName() {
        return "check_duplicate_rule";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();

        props.put("newRule", Map.of(
                "type", "object",
                "description", "The new rule to check for duplicates"
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Check if a new rule is duplicate with existing rules on the board. " +
                                "Analyzes trigger conditions and actions to determine if the rule already exists.")
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

            JsonNode newRuleNode = args.path("newRule");
            if (newRuleNode.isMissingNode() || newRuleNode.isNull()) {
                return errorJson("newRule is required", "VALIDATION_ERROR", 400);
            }

            log.info("=== CHECK DUPLICATE RULE DEBUG ===");
            log.info("User ID: {}", userId);

            // 解析新规则
            RuleDto newRule = objectMapper.convertValue(newRuleNode, RuleDto.class);
            
            if (!isValidRule(newRule)) {
                return errorJson("Invalid rule format", "VALIDATION_ERROR", 400);
            }

            log.info("New rule: trigger={}->{}, action={}",
                    getTriggerDescription(newRule),
                    getActionDescription(newRule));

            // 获取现有规则
            List<RuleDto> existingRules = safeList(boardStorageService.getRules(userId));
            
            log.info("Existing rules count: {}", existingRules.size());
            
            // 打印现有规则
            for (RuleDto rule : existingRules) {
                log.info("Existing rule: id={}, trigger={}->{}, action={}",
                        rule.getId(),
                        getTriggerDescription(rule),
                        getActionDescription(rule));
            }

            if (existingRules.isEmpty()) {
                // 没有现有规则，直接返回不重复
                return objectMapper.writeValueAsString(Map.of(
                        "isDuplicate", false,
                        "duplicateWith", null,
                        "similarity", 0.0,
                        "message", "No existing rules to compare. This is the first rule."
                ));
            }

            // 构建新规则信息
            String newRuleInfo = buildRuleInfoJson(newRule, "new");
            
            // 构建现有规则列表
            String existingRulesInfo = buildRulesListJson(existingRules);

            // 调用 Ark AI 进行重复检查
            String aiResponse = checkDuplicateWithAI(newRuleInfo, existingRulesInfo);

            log.info("AI Response: {}", aiResponse);

            // 解析 AI 响应
            String result = parseAiResponse(aiResponse, existingRules);
            
            log.info("Final Result: {}", result);
            
            return result;

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

    private boolean isValidRule(RuleDto rule) {
        if (rule == null) return false;
        if (rule.getConditions() == null || rule.getConditions().isEmpty()) return false;
        if (rule.getCommand() == null) return false;
        return true;
    }

    private String getTriggerDescription(RuleDto rule) {
        if (rule.getConditions() == null || rule.getConditions().isEmpty()) {
            return "none";
        }
        var cond = rule.getConditions().get(0);
        return String.format("%s.%s%s%s",
                cond.getDeviceName() != null ? cond.getDeviceName() : "",
                cond.getAttribute() != null ? cond.getAttribute() : "",
                cond.getRelation() != null ? cond.getRelation() : "",
                cond.getValue() != null ? cond.getValue() : "");
    }

    private String getActionDescription(RuleDto rule) {
        if (rule.getCommand() == null) {
            return "none";
        }
        return String.format("%s.%s(%s)",
                rule.getCommand().getDeviceName() != null ? rule.getCommand().getDeviceName() : "",
                rule.getCommand().getAction() != null ? rule.getCommand().getAction() : "",
                rule.getCommand().getContent() != null ? rule.getCommand().getContent() : "");
    }

    private String buildRuleInfoJson(RuleDto rule, String prefix) {
        try {
            Map<String, Object> ruleMap = new LinkedHashMap<>();
            ruleMap.put("ruleId", prefix + "_" + System.currentTimeMillis());
            
            // 条件
            if (rule.getConditions() != null && !rule.getConditions().isEmpty()) {
                List<Map<String, Object>> conditions = new ArrayList<>();
                for (var cond : rule.getConditions()) {
                    Map<String, Object> condMap = new LinkedHashMap<>();
                    condMap.put("deviceName", cond.getDeviceName());
                    condMap.put("attribute", cond.getAttribute());
                    condMap.put("relation", cond.getRelation());
                    condMap.put("value", cond.getValue());
                    conditions.add(condMap);
                }
                ruleMap.put("conditions", conditions);
            }
            
            // 命令
            if (rule.getCommand() != null) {
                Map<String, Object> commandMap = new LinkedHashMap<>();
                commandMap.put("deviceName", rule.getCommand().getDeviceName());
                commandMap.put("action", rule.getCommand().getAction());
                commandMap.put("contentDevice", rule.getCommand().getContentDevice());
                commandMap.put("content", rule.getCommand().getContent());
                ruleMap.put("command", commandMap);
            }
            
            return objectMapper.writeValueAsString(ruleMap);
        } catch (Exception e) {
            log.error("Failed to build rule info JSON", e);
            return "{}";
        }
    }

    private String buildRulesListJson(List<RuleDto> rules) {
        try {
            List<Map<String, Object>> rulesList = new ArrayList<>();
            
            for (RuleDto rule : rules) {
                Map<String, Object> ruleMap = new LinkedHashMap<>();
                ruleMap.put("ruleId", rule.getId() != null ? rule.getId() : "unknown");
                
                if (rule.getConditions() != null && !rule.getConditions().isEmpty()) {
                    List<Map<String, Object>> conditions = new ArrayList<>();
                    for (var cond : rule.getConditions()) {
                        Map<String, Object> condMap = new LinkedHashMap<>();
                        condMap.put("deviceName", cond.getDeviceName());
                        condMap.put("attribute", cond.getAttribute());
                        condMap.put("relation", cond.getRelation());
                        condMap.put("value", cond.getValue());
                        conditions.add(condMap);
                    }
                    ruleMap.put("conditions", conditions);
                }
                
                if (rule.getCommand() != null) {
                    Map<String, Object> commandMap = new LinkedHashMap<>();
                    commandMap.put("deviceName", rule.getCommand().getDeviceName());
                    commandMap.put("action", rule.getCommand().getAction());
                    commandMap.put("contentDevice", rule.getCommand().getContentDevice());
                    commandMap.put("content", rule.getCommand().getContent());
                    ruleMap.put("command", commandMap);
                }
                
                rulesList.add(ruleMap);
            }
            
            return objectMapper.writeValueAsString(rulesList);
        } catch (Exception e) {
            log.error("Failed to build rules list JSON", e);
            return "[]";
        }
    }

    private String checkDuplicateWithAI(String newRuleInfo, String existingRulesInfo) {
        String userPrompt = buildUserPrompt(newRuleInfo, existingRulesInfo);

        List<ChatMessage> messages = new ArrayList<>();
        messages.add(ChatMessage.builder().role(ChatMessageRole.SYSTEM).content(SYSTEM_PROMPT).build());
        messages.add(ChatMessage.builder().role(ChatMessageRole.USER).content(userPrompt).build());

        ChatCompletionRequest request = ChatCompletionRequest.builder()
                .model(arkAiClient.getModelId())
                .messages(messages)
                .temperature(0.3)
                .maxTokens(2000)
                .build();

        try {
            log.info("Calling Ark AI for duplicate rule check...");
            ChatCompletionResult result = arkAiClient.getArkService().createChatCompletion(request);
            if (result.getChoices() == null || result.getChoices().isEmpty()) {
                log.warn("AI returned empty choices");
                return "{\"isDuplicate\": false, \"similarity\": 0.0}";
            }
            
            ChatMessage responseMsg = result.getChoices().get(0).getMessage();
            if (responseMsg == null || responseMsg.getContent() == null) {
                log.warn("AI returned null message content");
                return "{\"isDuplicate\": false, \"similarity\": 0.0}";
            }
            
            String content = responseMsg.getContent().toString();
            log.info("AI response content length: {}", content.length());
            return content;
        } catch (Exception e) {
            log.error("Failed to call Ark AI for duplicate check", e);
            throw new RuntimeException("AI service unavailable: " + e.getMessage());
        }
    }

    private String buildUserPrompt(String newRuleInfo, String existingRulesInfo) {
        StringBuilder prompt = new StringBuilder();
        prompt.append("请检查新添加的规则是否与现有规则重复。\n\n");
        
        prompt.append("## 新添加的规则\n");
        prompt.append(newRuleInfo);
        prompt.append("\n\n");
        
        prompt.append("## 现有规则列表\n");
        prompt.append(existingRulesInfo);
        prompt.append("\n\n");
        
        prompt.append("请直接返回JSON格式的检查结果，不要包含其他文字。");
        
        return prompt.toString();
    }

    private String parseAiResponse(String aiResponse, List<RuleDto> existingRules) {
        try {
            // 清理 AI 返回的内容
            String cleanedResponse = aiResponse.trim();
            if (cleanedResponse.startsWith("```")) {
                int firstNewline = cleanedResponse.indexOf('\n');
                if (firstNewline > 0) {
                    cleanedResponse = cleanedResponse.substring(firstNewline).trim();
                }
            }
            if (cleanedResponse.endsWith("```")) {
                cleanedResponse = cleanedResponse.substring(0, cleanedResponse.lastIndexOf("```")).trim();
            }
            
            // 解析 JSON
            JsonNode root = objectMapper.readTree(cleanedResponse);
            
            boolean isDuplicate = root.path("isDuplicate").asBoolean(false);
            String duplicateWith = root.path("duplicateWith").asText(null);
            double similarity = root.path("similarity").asDouble(0.0);
            String reason = root.path("reason").asText("");

            // 如果 AI 返回了重复的规则 ID，验证它是否有效
            if (isDuplicate && duplicateWith != null && !duplicateWith.isBlank()) {
                Long targetId = parseLongSafely(duplicateWith);
                boolean validId = existingRules.stream()
                        .anyMatch(r -> r.getId() != null && r.getId().equals(targetId));
                if (!validId) {
                    // 如果 ID 无效，尝试找到最相似的规则
                    isDuplicate = similarity > 0.8;
                    duplicateWith = isDuplicate ? "unknown" : null;
                }
            }

            Map<String, Object> result = new LinkedHashMap<>();
            result.put("isDuplicate", isDuplicate);
            result.put("duplicateWith", duplicateWith);
            result.put("similarity", similarity);
            result.put("reason", reason);
            
            if (isDuplicate) {
                result.put("message", "This rule is duplicate with existing rule: " + duplicateWith);
            } else {
                result.put("message", "No duplicate rules found.");
            }

            return objectMapper.writeValueAsString(result);
            
        } catch (Exception e) {
            log.error("Failed to parse AI response", e);
            try {
                return objectMapper.writeValueAsString(Map.of(
                        "isDuplicate", false,
                        "similarity", 0.0,
                        "message", "Failed to check duplicate. Please try again."
                ));
            } catch (Exception ex) {
                return "{\"isDuplicate\":false,\"similarity\":0.0}";
            }
        }
    }

    private <T> List<T> safeList(List<T> list) {
        return list == null ? Collections.emptyList() : list;
    }

    private Long parseLongSafely(String value) {
        try {
            return value == null ? null : Long.valueOf(value.trim());
        } catch (NumberFormatException ignored) {
            return null;
        }
    }

    private String errorJson(String message, String errorCode, int status) {
        return AiToolResponseHelper.error(objectMapper, message, errorCode, status);
    }
}


