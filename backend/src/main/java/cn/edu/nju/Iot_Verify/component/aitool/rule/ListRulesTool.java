package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
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
import java.util.Locale;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class ListRulesTool implements AiTool {

    private final BoardStorageService boardStorageService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "list_rules";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("keyword", Map.of(
                "type", "string",
                "description", "Optional keyword to filter rules by device name, attribute, relation, value, or action. Leave empty to return all rules."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema("object", props, Collections.emptyList());

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("List automation rules on the current board.")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    public String execute(String argsJson) {
        try {
            Long userId = UserContextHolder.getUserId();
            if (userId == null) {
                return "{\"error\": \"User not logged in\"}";
            }

            JsonNode args = objectMapper.readTree(argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
            String keyword = args.path("keyword").asText("").trim().toLowerCase(Locale.ROOT);

            List<RuleDto> rules = safeList(boardStorageService.getRules(userId));
            if (!keyword.isEmpty()) {
                rules = rules.stream()
                        .filter(rule -> containsRuleKeyword(rule, keyword))
                        .toList();
            }

            if (rules.isEmpty()) {
                return "{\"message\": \"No rules found on the board.\", \"count\": 0}";
            }

            return objectMapper.writeValueAsString(Map.of(
                    "count", rules.size(),
                    "rules", rules
            ));
        } catch (Exception e) {
            log.error("list_rules failed", e);
            return "{\"error\": \"Failed to list rules: " + e.getMessage() + "\"}";
        }
    }

    private boolean containsRuleKeyword(RuleDto rule, String keyword) {
        if (rule == null) {
            return false;
        }
        if (contains(rule.getRuleString(), keyword)) {
            return true;
        }
        if (rule.getCommand() != null) {
            if (contains(rule.getCommand().getDeviceName(), keyword) || contains(rule.getCommand().getAction(), keyword)) {
                return true;
            }
        }
        if (rule.getConditions() != null) {
            for (RuleDto.Condition condition : rule.getConditions()) {
                if (condition == null) {
                    continue;
                }
                if (contains(condition.getDeviceName(), keyword)
                        || contains(condition.getAttribute(), keyword)
                        || contains(condition.getRelation(), keyword)
                        || contains(condition.getValue(), keyword)) {
                    return true;
                }
            }
        }
        return false;
    }

    private boolean contains(String value, String keyword) {
        return value != null && value.toLowerCase(Locale.ROOT).contains(keyword);
    }

    private <T> List<T> safeList(List<T> list) {
        return list == null ? List.of() : list;
    }
}
