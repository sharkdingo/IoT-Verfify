package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;

@Slf4j
@Component
public class ListRulesTool extends AbstractAiTool {

    private final BoardStorageService boardStorageService;

    public ListRulesTool(BoardStorageService boardStorageService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.boardStorageService = boardStorageService;
    }

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

    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }
            String keyword = args.path("keyword").asText("").trim().toLowerCase(Locale.ROOT);

            List<RuleDto> rules = safeList(boardStorageService.getRules(userId));
            if (!keyword.isEmpty()) {
                rules = rules.stream()
                        .filter(rule -> containsRuleKeyword(rule, keyword))
                        .toList();
            }

            if (rules.isEmpty()) {
                return objectMapper.writeValueAsString(Map.of(
                        "message", "No rules found on the board.",
                        "count", 0
                ));
            }

            return objectMapper.writeValueAsString(Map.of(
                    "count", rules.size(),
                    "rules", rules
            ));
        } catch (ServiceUnavailableException e) {
            log.warn("list_rules busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("list_rules business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("list_rules failed", e);
            return errorJson("Failed to list rules.", "INTERNAL_ERROR", 500);
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
}
