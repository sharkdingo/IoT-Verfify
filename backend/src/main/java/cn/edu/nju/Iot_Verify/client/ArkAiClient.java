package cn.edu.nju.Iot_Verify.client;

import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.*;
import com.volcengine.ark.runtime.service.ArkService;
import jakarta.annotation.PostConstruct;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.stereotype.Service;

import java.time.Duration;
import java.util.List;
import java.util.function.Consumer;
import java.util.stream.Collectors;

@Slf4j
@Service
public class ArkAiClient {

    @Value("${volcengine.ark.api-key}")
    private String apiKey;

    @Value("${volcengine.ark.model-id}")
    private String modelId;

    private ArkService arkService;

    // 用于 JSON 解析
    private final ObjectMapper objectMapper = new ObjectMapper();

    // 定义特殊的标记前缀，用于在 content 中区分普通文本和工具调用
    public static final String TOOL_CALLS_PREFIX = ":::TOOL_CALLS:::";
    public static final String TOOL_RESULT_SEPARATOR = ":::ID_SEP:::";

    @PostConstruct
    public void init() {
        this.arkService = ArkService.builder()
                .apiKey(apiKey)
                .timeout(Duration.ofMinutes(5))
                .build();
        log.info("ArkAiClient initialized with Model ID: {}", modelId);
    }

    public ChatCompletionResult checkIntent(List<ChatMessage> messages, List<ChatTool> tools) {
        ChatCompletionRequest request = ChatCompletionRequest.builder()
                .model(modelId)
                .messages(messages)
                .tools(tools)
                .build();
        return arkService.createChatCompletion(request);
    }

    public void streamChat(List<ChatMessage> messages, Consumer<String> onNext) {
        ChatCompletionRequest request = ChatCompletionRequest.builder()
                .model(modelId)
                .messages(messages)
                .build();

        log.info(">>> 开始调用流式对话，消息数量: {}", messages.size()); // Debug 日志

        arkService.streamChatCompletion(request)
                .doOnError(e -> log.error("Stream chat error", e))
                .blockingForEach(choice -> {
                    if (!choice.getChoices().isEmpty()) {
                        ChatMessage msg = choice.getChoices().get(0).getMessage();

                        // Debug 日志：看看原始返回是啥
                        log.info("<<< AI原始响应片段: {}", msg.getContent());

                        Object contentObj = msg.getContent();
                        String delta = contentObj != null ? contentObj.toString() : "";

                        if (!delta.isEmpty()) {
                            onNext.accept(delta);
                        }
                    }
                });

        log.info(">>> 流式对话结束"); // Debug 日志
    }

    /**
     * 【核心修改】将 PO 转换为 SDK 消息
     * 这里包含了"反序列化"逻辑，从简单的 String content 还原出复杂的 Tool 结构
     */
    public List<ChatMessage> convertToSdkMessages(List<ChatMessagePo> poList) {
        return poList.stream()
                .map(this::mapPoToSdkMessage)
                .collect(Collectors.toList());
    }

    private ChatMessage mapPoToSdkMessage(ChatMessagePo po) {
        String roleStr = po.getRole() == null ? "user" : po.getRole().toLowerCase();
        String content = po.getContent() == null ? "" : po.getContent();

        // 1. 处理 TOOL 角色 (工具执行结果)
        // 存储格式约定: toolCallId + ":::ID_SEP:::" + jsonResult
        if ("tool".equals(roleStr)) {
            String toolCallId = "";
            String toolContent = content;

            // 尝试拆分 ID 和 内容
            if (content.contains(TOOL_RESULT_SEPARATOR)) {
                String[] parts = content.split(TOOL_RESULT_SEPARATOR, 2);
                toolCallId = parts[0];
                toolContent = parts[1];
            }

            return ChatMessage.builder()
                    .role(ChatMessageRole.TOOL)
                    .content(toolContent)
                    .toolCallId(toolCallId)
                    .build();
        }

        // 2. 处理 ASSISTANT 角色 (可能包含 ToolCalls 请求)
        // 存储格式约定: ":::TOOL_CALLS:::" + jsonList
        if ("assistant".equals(roleStr)) {
            if (content.startsWith(TOOL_CALLS_PREFIX)) {
                try {
                    String json = content.substring(TOOL_CALLS_PREFIX.length());
                    List<ChatToolCall> toolCalls = objectMapper.readValue(json, new TypeReference<List<ChatToolCall>>() {});

                    return ChatMessage.builder()
                            .role(ChatMessageRole.ASSISTANT)
                            .content("") // ToolCall 消息通常 content 为空
                            .toolCalls(toolCalls)
                            .build();
                } catch (Exception e) {
                    log.error("Failed to parse tool calls from history", e);
                    // 解析失败降级为普通文本
                    return ChatMessage.builder().role(ChatMessageRole.ASSISTANT).content(content).build();
                }
            }
        }

        // 3. 普通 USER 或 ASSISTANT 消息
        ChatMessageRole roleEnum = ChatMessageRole.USER;
        try {
            roleEnum = ChatMessageRole.valueOf(roleStr.toUpperCase());
        } catch (Exception e) { /* ignore */ }

        return ChatMessage.builder()
                .role(roleEnum)
                .content(content)
                .build();
    }
}