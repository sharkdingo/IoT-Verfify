package cn.edu.nju.Iot_Verify.component.ai;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolCall;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;

/**
 * Single owner of the on-disk chat-message wire format and the {@link ChatMessagePo} ⇄
 * {@link LlmMessage} conversion. Concentrating this here keeps both the persistence format
 * and history reconstruction in one cohesive place and free of any vendor SDK type.
 *
 * <p>Two persisted encodings are understood, for backward compatibility with existing rows:
 * <ul>
 *   <li><b>structured</b> (current): a JSON object {@code {"type":"tool_calls"|"tool_result", ...}};</li>
 *   <li><b>legacy</b>: a {@code :::TOOL_CALLS:::}-prefixed body, or a
 *       {@code toolCallId:::ID_SEP:::result} separator form.</li>
 * </ul>
 * New rows are always written in the structured form via the {@code serialize*} methods.
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class LlmMessageCodec {

    // legacy serialization format
    public static final String TOOL_CALLS_PREFIX = ":::TOOL_CALLS:::";
    public static final String TOOL_RESULT_SEPARATOR = ":::ID_SEP:::";

    // structured serialization format
    public static final String TOOL_CALLS_JSON_TYPE = "tool_calls";
    public static final String TOOL_RESULT_JSON_TYPE = "tool_result";

    private final ObjectMapper objectMapper;

    // ── PO → domain ──────────────────────────────────────────────────────

    public List<LlmMessage> toMessages(List<ChatMessagePo> poList) {
        List<LlmMessage> messages = new ArrayList<>(poList.size());
        for (ChatMessagePo po : poList) {
            messages.add(toMessage(po));
        }
        return messages;
    }

    public LlmMessage toMessage(ChatMessagePo po) {
        String roleStr = po.getRole() == null ? "user" : po.getRole().toLowerCase(Locale.ROOT);
        String content = po.getContent() == null ? "" : po.getContent();

        if ("tool".equals(roleStr)) {
            ToolResultParts parts = parseToolResult(content);
            return LlmMessage.tool(parts.toolCallId(), parts.result());
        }

        if ("assistant".equals(roleStr)) {
            List<LlmToolCall> toolCalls = parseAssistantToolCalls(content);
            if (toolCalls != null) {
                return LlmMessage.assistantToolCalls(toolCalls);
            }
            return LlmMessage.assistant(content);
        }

        return switch (roleStr) {
            case "system" -> LlmMessage.system(content);
            case "user" -> LlmMessage.user(content);
            default -> {
                log.warn("Unknown chat message role '{}', defaulting to USER", roleStr);
                yield LlmMessage.user(content);
            }
        };
    }

    // ── domain → persisted content ───────────────────────────────────────

    /** Serialize an assistant tool-call request for persistence (structured form). */
    public String serializeToolCalls(List<LlmToolCall> toolCalls) {
        try {
            List<Map<String, Object>> calls = new ArrayList<>();
            for (LlmToolCall c : toolCalls) {
                calls.add(Map.of(
                        "id", c.id(),
                        "type", "function",
                        "function", Map.of("name", c.name(), "arguments", c.argumentsJson())));
            }
            return objectMapper.writeValueAsString(Map.of(
                    "type", TOOL_CALLS_JSON_TYPE,
                    "toolCalls", calls));
        } catch (Exception e) {
            log.warn("Failed to serialize tool calls, persisting empty placeholder", e);
            return "{\"type\":\"" + TOOL_CALLS_JSON_TYPE + "\",\"toolCalls\":[]}";
        }
    }

    /** Serialize a tool-execution result for persistence (structured form). */
    public String serializeToolResult(String toolCallId, String result) {
        try {
            return objectMapper.writeValueAsString(Map.of(
                    "type", TOOL_RESULT_JSON_TYPE,
                    "toolCallId", toolCallId == null ? "" : toolCallId,
                    "result", result == null ? "" : result));
        } catch (Exception e) {
            return (toolCallId == null ? "" : toolCallId) + TOOL_RESULT_SEPARATOR + (result == null ? "" : result);
        }
    }

    // ── classification helpers (used by history windowing / frontend filtering) ──

    public boolean isToolResultContent(ChatMessagePo po) {
        return po != null && "tool".equalsIgnoreCase(po.getRole());
    }

    public boolean isAssistantToolCallContent(ChatMessagePo po) {
        if (po == null || !"assistant".equalsIgnoreCase(po.getRole())) {
            return false;
        }
        String content = po.getContent() == null ? "" : po.getContent();
        if (content.startsWith(TOOL_CALLS_PREFIX)) {
            return true;
        }
        try {
            JsonNode root = objectMapper.readTree(content);
            return root.isObject()
                    && TOOL_CALLS_JSON_TYPE.equals(root.path("type").asText(""))
                    && root.has("toolCalls");
        } catch (Exception ignore) {
            return false;
        }
    }

    // ── internal parsing ─────────────────────────────────────────────────

    private ToolResultParts parseToolResult(String content) {
        if (content != null && !content.isEmpty() && content.stripLeading().startsWith("{")) {
            try {
                JsonNode root = objectMapper.readTree(content);
                if (root.isObject() && TOOL_RESULT_JSON_TYPE.equals(root.path("type").asText(""))) {
                    return new ToolResultParts(root.path("toolCallId").asText(""),
                            root.path("result").asText(""));
                }
            } catch (Exception e) {
                log.debug("Tool message is not structured JSON, falling back to separator parsing", e);
            }
        }
        if (content != null && content.contains(TOOL_RESULT_SEPARATOR)) {
            String[] parts = content.split(TOOL_RESULT_SEPARATOR, 2);
            return new ToolResultParts(parts[0], parts.length > 1 ? parts[1] : "");
        }
        return new ToolResultParts("", content != null ? content : "");
    }

    private List<LlmToolCall> parseAssistantToolCalls(String content) {
        if (content != null && !content.isEmpty() && content.stripLeading().startsWith("{")) {
            try {
                JsonNode root = objectMapper.readTree(content);
                if (root.isObject() && TOOL_CALLS_JSON_TYPE.equals(root.path("type").asText(""))
                        && root.has("toolCalls")) {
                    return extractCalls(root.path("toolCalls"));
                }
            } catch (Exception e) {
                log.debug("Assistant content is not structured tool-calls JSON, trying legacy format", e);
            }
        }
        if (content != null && content.startsWith(TOOL_CALLS_PREFIX)) {
            try {
                JsonNode arr = objectMapper.readTree(content.substring(TOOL_CALLS_PREFIX.length()));
                return extractCalls(arr);
            } catch (Exception e) {
                log.error("Failed to parse legacy tool calls from history", e);
            }
        }
        return null;
    }

    private List<LlmToolCall> extractCalls(JsonNode toolCallsNode) {
        List<LlmToolCall> calls = new ArrayList<>();
        if (toolCallsNode != null && toolCallsNode.isArray()) {
            for (JsonNode node : toolCallsNode) {
                JsonNode fn = node.path("function");
                calls.add(new LlmToolCall(
                        node.path("id").asText(""),
                        fn.path("name").asText(""),
                        fn.path("arguments").asText("")));
            }
        }
        return calls;
    }

    private record ToolResultParts(String toolCallId, String result) {
    }
}
