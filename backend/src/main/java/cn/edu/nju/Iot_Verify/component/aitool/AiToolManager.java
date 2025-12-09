package cn.edu.nju.Iot_Verify.component.aitool;

import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import jakarta.annotation.PostConstruct;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;

@Slf4j
@Component
@RequiredArgsConstructor
public class AiToolManager {

    // Spring 会自动注入所有实现了 AiTool 接口的 Bean (例如 AddNodeTool)
    private final List<AiTool> allTools;

    // 缓存 Map：ToolName -> AiTool 实例
    private Map<String, AiTool> toolMap;

    @PostConstruct
    public void init() {
        toolMap = allTools.stream()
                .collect(Collectors.toMap(AiTool::getName, Function.identity()));
    }

    /**
     * 获取所有工具的定义列表 (提供给 ArkAiClient 使用)
     */
    public List<ChatTool> getAllToolDefinitions() {
        return allTools.stream()
                .map(AiTool::getDefinition)
                .collect(Collectors.toList());
    }

    /**
     * 根据工具名和 JSON 参数执行具体的工具
     */
    public String execute(String functionName, String argsJson) {
        AiTool tool = toolMap.get(functionName);
        if (tool == null) {
            log.warn("AI 尝试调用不存在的工具: {}", functionName);
            return "{\"error\": \"Unknown function: " + functionName + "\"}";
        }

        log.info("开始执行 AI 工具: {}", functionName);
        return tool.execute(argsJson);
    }
}