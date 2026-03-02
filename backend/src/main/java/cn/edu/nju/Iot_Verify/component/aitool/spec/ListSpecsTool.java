package cn.edu.nju.Iot_Verify.component.aitool.spec;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
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
public class ListSpecsTool implements AiTool {

    private final BoardStorageService boardStorageService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "list_specs";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("keyword", Map.of(
                "type", "string",
                "description", "Optional keyword to filter specifications by ID, template label, device, key, relation, or value. Leave empty to return all."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema("object", props, Collections.emptyList());

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("List formal specifications on the current board.")
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

            List<SpecificationDto> specs = safeList(boardStorageService.getSpecs(userId));
            if (!keyword.isEmpty()) {
                specs = specs.stream()
                        .filter(spec -> containsSpecKeyword(spec, keyword))
                        .toList();
            }

            if (specs.isEmpty()) {
                return "{\"message\": \"No specifications found on the board.\", \"count\": 0}";
            }

            return objectMapper.writeValueAsString(Map.of(
                    "count", specs.size(),
                    "specs", specs
            ));
        } catch (Exception e) {
            log.error("list_specs failed", e);
            return "{\"error\": \"Failed to list specs: " + e.getMessage() + "\"}";
        }
    }

    private boolean containsSpecKeyword(SpecificationDto spec, String keyword) {
        if (spec == null) {
            return false;
        }
        if (contains(spec.getId(), keyword)
                || contains(spec.getTemplateId(), keyword)
                || contains(spec.getTemplateLabel(), keyword)) {
            return true;
        }
        return containsConditions(spec.getAConditions(), keyword)
                || containsConditions(spec.getIfConditions(), keyword)
                || containsConditions(spec.getThenConditions(), keyword);
    }

    private boolean containsConditions(List<SpecConditionDto> conditions, String keyword) {
        if (conditions == null) {
            return false;
        }
        for (SpecConditionDto condition : conditions) {
            if (condition == null) {
                continue;
            }
            if (contains(condition.getDeviceId(), keyword)
                    || contains(condition.getDeviceLabel(), keyword)
                    || contains(condition.getTargetType(), keyword)
                    || contains(condition.getKey(), keyword)
                    || contains(condition.getRelation(), keyword)
                    || contains(condition.getValue(), keyword)) {
                return true;
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
