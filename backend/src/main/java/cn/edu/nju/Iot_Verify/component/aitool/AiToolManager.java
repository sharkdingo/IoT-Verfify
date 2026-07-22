package cn.edu.nju.Iot_Verify.component.aitool;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.configure.ChatExecutionConfig;
import com.fasterxml.jackson.databind.ObjectMapper;
import jakarta.annotation.PostConstruct;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.List;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.nio.charset.StandardCharsets;
import java.util.function.Function;
import java.util.stream.Collectors;

@Slf4j
@Component
@RequiredArgsConstructor
public class AiToolManager {

    private static final Set<String> MUTATION_CAPABLE_TOOLS = Set.of(
            "add_device", "delete_device", "manage_environment", "apply_scenario",
            "reset_default_templates", "manage_spec", "add_template", "delete_template",
            "delete_trace", "cancel_verify_task", "fix_violation", "manage_rule",
            "delete_simulation_trace", "cancel_simulate_task", "verify_model",
            "verify_model_async", "simulate_model", "simulate_model_async");

    // Spring 会自动注入所有实现了 AiTool 接口的 Bean (例如 AddNodeTool)
    private final List<AiTool> allTools;
    private final ObjectMapper objectMapper;
    private final ChatExecutionConfig chatExecutionConfig;

    // 缓存 Map：ToolName -> AiTool 实例
    private Map<String, AiTool> toolMap;

    @PostConstruct
    public void init() {
        toolMap = allTools.stream()
                .collect(Collectors.toMap(AiTool::getName, Function.identity()));
    }

    /**
     * 获取所有工具的定义列表 (提供给 LlmProvider 使用)
     */
    public List<LlmToolSpec> getAllToolDefinitions() {
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
            return errorJson("Unknown function: " + functionName, "TOOL_NOT_FOUND", 404);
        }

        log.info("开始执行 AI 工具: {}", functionName);
        try {
            return boundResult(functionName, tool.execute(argsJson));
        } catch (Exception e) {
            log.error("AI tool '{}' threw unexpected exception", functionName, e);
            return errorJson("Tool execution failed due to an internal error", "TOOL_EXECUTION_ERROR", 500);
        }
    }

    private String boundResult(String functionName, String result) {
        String safeResult = result == null ? "" : result;
        int resultBytes = safeResult.getBytes(StandardCharsets.UTF_8).length;
        if (resultBytes <= chatExecutionConfig.getMaxToolResultBytes()) {
            return safeResult;
        }

        boolean mutationMayHaveCommitted = MUTATION_CAPABLE_TOOLS.contains(functionName);
        log.warn("AI tool '{}' result exceeded persistence/model limit: bytes={}, limit={}",
                functionName, resultBytes, chatExecutionConfig.getMaxToolResultBytes());
        Map<String, Object> body = new LinkedHashMap<>();
        body.put("resultStatus", "RESULT_UNAVAILABLE");
        body.put("resultAvailable", false);
        body.put("mutationMayHaveCommitted", mutationMayHaveCommitted);
        body.put("errorCode", "TOOL_RESULT_TOO_LARGE");
        body.put("message", mutationMayHaveCommitted
                ? "Tool result details exceeded the safe size limit. The operation may already have changed state; refresh current state before retrying with a narrower request."
                : "Tool result details exceeded the safe size limit. Retry with a narrower filter or request fewer details.");
        body.put("resultBytes", resultBytes);
        body.put("maxResultBytes", chatExecutionConfig.getMaxToolResultBytes());
        return AiToolResponseHelper.success(objectMapper, body, "Tool result exceeded the safe size limit.",
                mutationMayHaveCommitted);
    }

    private String errorJson(String message, String errorCode, int status) {
        return AiToolResponseHelper.error(objectMapper, message, errorCode, status);
    }
}
