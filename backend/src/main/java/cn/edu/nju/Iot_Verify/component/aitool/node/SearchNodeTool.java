package cn.edu.nju.Iot_Verify.component.aitool.node;

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.NodeService;
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
import java.util.LinkedHashMap;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class SearchNodeTool implements AiTool {

    private final NodeService nodeService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "search_devices";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("keyword", Map.of(
                "type", "string",
                "description", "Device template keyword (e.g. 'AC Cooler') or device name. Leave empty to return all devices."
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("Search devices on the canvas, supports filtering by template type or name")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    public String execute(String argsJson) {
        try {
            Long userId = UserContextHolder.getUserId();
            if (userId == null) {
                return errorJson("User not logged in");
            }

            JsonNode args = objectMapper.readTree(argsJson == null || argsJson.isBlank() ? "{}" : argsJson);
            String keyword = args.path("keyword").asText("").trim();
            log.info("Executing search_devices, keyword: {}", keyword);
            String raw = nodeService.searchNodes(userId, keyword);
            return normalizeResult(raw);
        } catch (Exception e) {
            log.error("search_devices failed", e);
            return errorJson("Search devices failed. Please retry.");
        }
    }

    private String normalizeResult(String raw) throws Exception {
        if (raw == null || raw.isBlank()) {
            return objectMapper.writeValueAsString(Map.of("count", 0, "devices", Collections.emptyList()));
        }
        try {
            JsonNode root = objectMapper.readTree(raw);
            if (root.isArray()) {
                return objectMapper.writeValueAsString(Map.of(
                        "count", root.size(),
                        "devices", root
                ));
            }
            if (root.isObject()) {
                return raw;
            }
        } catch (Exception ignore) {
        }

        Map<String, Object> body = new LinkedHashMap<>();
        body.put("message", raw);
        body.put("count", 0);
        body.put("devices", Collections.emptyList());
        return objectMapper.writeValueAsString(body);
    }

    private String errorJson(String message) {
        try {
            return objectMapper.writeValueAsString(Map.of("error", message));
        } catch (Exception ex) {
            return "{\"error\":\"" + message + "\"}";
        }
    }
}
