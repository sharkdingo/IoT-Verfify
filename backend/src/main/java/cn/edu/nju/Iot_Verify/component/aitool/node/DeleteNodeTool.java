package cn.edu.nju.Iot_Verify.component.aitool.node; // 【变化】包名精确到 node

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
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
public class DeleteNodeTool implements AiTool {

    private final NodeService nodeService;
    private final ObjectMapper objectMapper;

    @Override
    public String getName() {
        return "delete_device";
    }

    @Override
    public ChatTool getDefinition() {
        Map<String, Object> props = new HashMap<>();
        props.put("label", Map.of("type", "string", "description", "设备名称（标签）"));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Collections.singletonList("label")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("删除设备结点")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    public String execute(String argsJson) {
        try {
            JsonNode args = objectMapper.readTree(argsJson);
            String label = args.path("label").asText();
            if (label == null || label.isEmpty()) return "{\"error\": \"缺少label\"}";

            log.info("执行工具 delete_device, label: {}", label);
            return nodeService.deleteNode(label);
        } catch (Exception e) {
            log.error("delete_device 执行失败", e);
            return "{\"error\": \"删除失败: " + e.getMessage() + "\"}";
        }
    }
}