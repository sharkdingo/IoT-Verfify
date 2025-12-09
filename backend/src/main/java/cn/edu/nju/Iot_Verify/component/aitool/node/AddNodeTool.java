package cn.edu.nju.Iot_Verify.component.aitool.node; // 【变化】包名精确到 node

import cn.edu.nju.Iot_Verify.component.aitool.AiTool;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.service.NodeService;
import cn.edu.nju.Iot_Verify.util.FunctionParameterSchema;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatFunction;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

@Slf4j
@Component
@RequiredArgsConstructor
public class AddNodeTool implements AiTool {

    private final NodeService nodeService;
    private final ObjectMapper objectMapper;
    private final DeviceTemplateRepository templateRepo;

    @Override
    public String getName() {
        return "add_device";
    }

    @Override
    public ChatTool getDefinition() {
        List<String> validTemplates = templateRepo.findAllNames();
        String templateListStr = String.join(", ", validTemplates);

        Map<String, Object> props = new HashMap<>();

        // 优化 Prompt：明确告知有哪些合法值
        props.put("templateName", Map.of(
                "type", "string",
                "description", "设备模板类型名称。系统仅支持以下标准模板：[" + templateListStr + "]。" +
                        "请根据语义自动将用户输入的别名映射为列表中的标准名称。" +
                        "如果用户请求的设备与列表中任何一个模板都在语义上完全不相关（例如列表中只有空调，用户却要咖啡机），" +
                        "请直接传入用户所说的原始名称，不要强行匹配。"
        ));

        props.put("label", Map.of(
                "type", "string",
                "description", "设备显示名称"
        ));

        props.put("x", Map.of("type", "number", "description", "X坐标（默认150）"));
        props.put("y", Map.of("type", "number", "description", "Y坐标（默认150）"));
        props.put("w", Map.of("type", "integer", "description", "宽度（默认110）"));
        props.put("h", Map.of("type", "integer", "description", "高度（默认90）"));

        props.put("state", Map.of("type", "string", "description", "设备的初始状态。如果用户未指定，请留空（null），系统将自动读取该设备的默认配置。"));

        FunctionParameterSchema schema = new FunctionParameterSchema(
                "object", props, Arrays.asList("templateName", "label")
        );

        return new ChatTool(
                "function",
                new ChatFunction.Builder()
                        .name(getName())
                        .description("添加一个新的设备")
                        .parameters(schema)
                        .build()
        );
    }

    @Override
    public String execute(String argsJson) {
        try {
            JsonNode args = objectMapper.readTree(argsJson);
            String templateName = args.path("templateName").asText();
            String label = args.path("label").asText();

            // 安全读取数值
            Double x = args.has("x") ? args.path("x").asDouble() : null;
            Double y = args.has("y") ? args.path("y").asDouble() : null;
            Integer w = args.has("w") ? args.path("w").asInt() : null;
            Integer h = args.has("h") ? args.path("h").asInt() : null;
            String state = args.has("state") ? args.path("state").asText() : null;

            log.info("执行工具 add_device: {}", label);

            // 调用 Service，Service 会返回包含提醒的字符串
            return nodeService.addNode(templateName, label, x, y, state, w, h);

        } catch (Exception e) {
            log.error("add_device 执行失败", e);
            return "{\"error\": \"添加失败: " + e.getMessage() + "\"}";
        }
    }
}