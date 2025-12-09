package cn.edu.nju.Iot_Verify.component.aitool.node; // 【变化】包名精确到 node

import cn.edu.nju.Iot_Verify.component.aitool.AiTool; // 需要 import 上级包的接口
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
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class SearchNodeTool implements AiTool {

    private final NodeService nodeService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "search_devices"; // AI 以后会输出这个名字
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("keyword", Map.of(
                "type", "string",
                "description", "设备模板关键词（如 'AC Cooler'）或设备名称。如果不填则返回所有设备。"
        ));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.emptyList()
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("搜索当前画布上的设备列表，支持按模板类型或名称搜索")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    public String execute(String argsJson) {
        try {
            JsonNode args = objectMapper.readTree(argsJson);
            String keyword = args.path("keyword").asText("");
            log.info("执行工具 search_devices, keyword: {}", keyword);
            return nodeService.searchNodes(keyword);
        } catch (Exception e) {
            log.error("search_devices 执行失败", e); // 修正日志名
            return "{\"error\": \"查询失败: " + e.getMessage() + "\"}";
        }
    }
}