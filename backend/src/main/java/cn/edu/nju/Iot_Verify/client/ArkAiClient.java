package cn.edu.nju.Iot_Verify.client;

import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionRequest;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionResult;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessage;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessageRole;
import com.volcengine.ark.runtime.model.completion.chat.ChatTool;
import com.volcengine.ark.runtime.model.completion.chat.ChatToolCall;
import com.volcengine.ark.runtime.service.ArkService;
import jakarta.annotation.PostConstruct;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.stereotype.Service;

import java.time.Duration;
import java.util.List;
import java.util.Locale;
import java.util.function.Consumer;
import java.util.stream.Collectors;

@Slf4j
@Service
public class ArkAiClient {

    @Value("${volcengine.ark.api-key}")
    private String apiKey;

    @Value("${volcengine.ark.model-id}")
    private String modelId;

    @Value("${volcengine.ark.base-url:https://ark.cn-beijing.volces.com}")
    private String baseUrl;

    private ArkService arkService;

    private final ObjectMapper objectMapper = new ObjectMapper();

    // legacy serialization format
    public static final String TOOL_CALLS_PREFIX = ":::TOOL_CALLS:::";
    public static final String TOOL_RESULT_SEPARATOR = ":::ID_SEP:::";

    // new structured serialization format
    public static final String TOOL_CALLS_JSON_TYPE = "tool_calls";
    public static final String TOOL_RESULT_JSON_TYPE = "tool_result";

    @PostConstruct
    public void init() {
        String normalizedBaseUrl = normalizeArkBaseUrl(baseUrl);
        this.arkService = ArkService.builder()
                .apiKey(apiKey)
                .baseUrl(normalizedBaseUrl)
                .timeout(Duration.ofMinutes(5))
                .build();
        log.info("ArkAiClient initialized with Model ID: {}, Base URL: {}", modelId, normalizedBaseUrl);
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

        arkService.streamChatCompletion(request)
                .doOnError(e -> log.error("Stream chat error", e))
                .blockingForEach(choice -> {
                    if (choice.getChoices().isEmpty()) {
                        return;
                    }
                    ChatMessage msg = choice.getChoices().get(0).getMessage();
                    String delta = msg != null && msg.getContent() != null ? msg.getContent().toString() : "";
                    if (!delta.isEmpty()) {
                        onNext.accept(delta);
                    }
                });
    }

    public List<ChatMessage> convertToSdkMessages(List<ChatMessagePo> poList) {
        return poList.stream()
                .map(this::mapPoToSdkMessage)
                .collect(Collectors.toList());
    }

    private ChatMessage mapPoToSdkMessage(ChatMessagePo po) {
        String roleStr = po.getRole() == null ? "user" : po.getRole().toLowerCase(Locale.ROOT);
        String content = po.getContent() == null ? "" : po.getContent();

        if ("tool".equals(roleStr)) {
            ToolMessageParts parts = parseToolMessage(content);
            return ChatMessage.builder()
                    .role(ChatMessageRole.TOOL)
                    .content(parts.toolContent())
                    .toolCallId(parts.toolCallId())
                    .build();
        }

        if ("assistant".equals(roleStr)) {
            List<ChatToolCall> toolCalls = parseAssistantToolCalls(content);
            if (toolCalls != null) {
                return ChatMessage.builder()
                        .role(ChatMessageRole.ASSISTANT)
                        .content("")
                        .toolCalls(toolCalls)
                        .build();
            }
        }

        ChatMessageRole roleEnum = ChatMessageRole.USER;
        try {
            roleEnum = ChatMessageRole.valueOf(roleStr.toUpperCase(Locale.ROOT));
        } catch (Exception ignore) {
        }

        return ChatMessage.builder()
                .role(roleEnum)
                .content(content)
                .build();
    }

    private ToolMessageParts parseToolMessage(String content) {
        try {
            JsonNode root = objectMapper.readTree(content);
            if (root.isObject() && TOOL_RESULT_JSON_TYPE.equals(root.path("type").asText(""))) {
                String toolCallId = root.path("toolCallId").asText("");
                String result = root.path("result").asText("");
                return new ToolMessageParts(toolCallId, result);
            }
        } catch (Exception ignore) {
        }

        if (content.contains(TOOL_RESULT_SEPARATOR)) {
            String[] parts = content.split(TOOL_RESULT_SEPARATOR, 2);
            return new ToolMessageParts(parts[0], parts.length > 1 ? parts[1] : "");
        }

        return new ToolMessageParts("", content);
    }

    private List<ChatToolCall> parseAssistantToolCalls(String content) {
        // new structured JSON
        try {
            JsonNode root = objectMapper.readTree(content);
            if (root.isObject() && TOOL_CALLS_JSON_TYPE.equals(root.path("type").asText("")) && root.has("toolCalls")) {
                return objectMapper.convertValue(root.path("toolCalls"), new TypeReference<List<ChatToolCall>>() {
                });
            }
        } catch (Exception ignore) {
        }

        // legacy prefixed format
        if (content.startsWith(TOOL_CALLS_PREFIX)) {
            try {
                String json = content.substring(TOOL_CALLS_PREFIX.length());
                return objectMapper.readValue(json, new TypeReference<List<ChatToolCall>>() {
                });
            } catch (Exception e) {
                log.error("Failed to parse tool calls from history", e);
            }
        }

        return null;
    }

    private String normalizeArkBaseUrl(String configuredBaseUrl) {
        String trimmed = configuredBaseUrl == null ? "" : configuredBaseUrl.trim();
        if (trimmed.isEmpty()) {
            return "https://ark.cn-beijing.volces.com";
        }

        String normalized = trimmed.endsWith("/")
                ? trimmed.substring(0, trimmed.length() - 1)
                : trimmed;

        if (normalized.toLowerCase(Locale.ROOT).endsWith("/api/v3")) {
            String fixed = normalized.substring(0, normalized.length() - "/api/v3".length());
            log.warn("volcengine.ark.base-url should not contain '/api/v3'. Auto-corrected from '{}' to '{}'.",
                    configuredBaseUrl, fixed);
            return fixed;
        }
        return normalized;
    }

    private record ToolMessageParts(String toolCallId, String toolContent) {
    }
}
