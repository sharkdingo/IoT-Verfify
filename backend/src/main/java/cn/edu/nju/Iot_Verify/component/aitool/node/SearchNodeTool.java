package cn.edu.nju.Iot_Verify.component.aitool.node;

import cn.edu.nju.Iot_Verify.component.aitool.AbstractAiTool;
import cn.edu.nju.Iot_Verify.exception.BaseException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.NodeService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;

@Slf4j
@Component
public class SearchNodeTool extends AbstractAiTool {

    private final NodeService nodeService;

    public SearchNodeTool(NodeService nodeService, ObjectMapper objectMapper) {
        super(objectMapper);
        this.nodeService = nodeService;
    }

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
    protected String doExecute(Long userId, String argsJson) {
        try {
            JsonNode args;
            try {
                args = parseArgs(argsJson);
            } catch (ArgParseException e) {
                return e.getErrorResponse();
            }
            String keyword = args.path("keyword").asText("").trim();
            log.info("Executing search_devices, keyword: {}", keyword);
            String raw = nodeService.searchNodes(userId, keyword);
            return normalizeResult(raw);
        } catch (ServiceUnavailableException e) {
            log.warn("search_devices busy: {}", e.getMessage());
            return errorJson(e.getMessage(), "SERVICE_UNAVAILABLE", 503);
        } catch (BaseException e) {
            log.warn("search_devices business error [{}]: {}", e.getCode(), e.getMessage());
            return errorJson(e.getMessage(), "BUSINESS_ERROR", e.getCode());
        } catch (Exception e) {
            log.error("search_devices failed", e);
            return errorJson("Search devices failed. Please retry.", "INTERNAL_ERROR", 500);
        }
    }

    private String normalizeResult(String raw) throws Exception {
        if (raw == null || raw.isBlank()) {
            return objectMapper.writeValueAsString(Map.of("count", 0, "devices", Collections.emptyList()));
        }
        JsonNode root;
        try {
            root = objectMapper.readTree(raw);
        } catch (Exception ignore) {
            Map<String, Object> body = new LinkedHashMap<>();
            body.put("message", raw);
            body.put("count", 0);
            body.put("devices", Collections.emptyList());
            return objectMapper.writeValueAsString(body);
        }
        if (root.isArray()) {
            return objectMapper.writeValueAsString(Map.of("count", root.size(), "devices", root));
        }
        if (root.isObject()) {
            return raw;
        }
        Map<String, Object> body = new LinkedHashMap<>();
        body.put("message", raw);
        body.put("count", 0);
        body.put("devices", Collections.emptyList());
        return objectMapper.writeValueAsString(body);
    }
}
