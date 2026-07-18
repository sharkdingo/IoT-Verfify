package cn.edu.nju.Iot_Verify.component.ai.model;

import java.util.List;

/**
 * Provider-agnostic non-streaming chat-completion result.
 *
 * <p>A response may contain text, tool calls, or both:
 * <ul>
 *   <li>the model returned text → {@code text} is non-blank, {@code toolCalls} empty;</li>
 *   <li>the model requested tools → {@code toolCalls} is non-empty;</li>
 *   <li>ReAct-capable providers may attach a user-visible reasoning summary in {@code text}
 *       alongside the tool calls.</li>
 * </ul>
 * An empty/absent choice from the provider maps to {@link #empty()}.
 *
 * @param text      assistant text content (never null; empty when no visible summary was returned)
 * @param toolCalls tool-call requests (never null; empty when the model replied with text)
 */
public record LlmChatResponse(String text, List<LlmToolCall> toolCalls) {

    public LlmChatResponse {
        text = text == null ? "" : text;
        toolCalls = toolCalls == null ? List.of() : List.copyOf(toolCalls);
    }

    public static LlmChatResponse ofText(String text) {
        return new LlmChatResponse(text, List.of());
    }

    public static LlmChatResponse ofToolCalls(List<LlmToolCall> toolCalls) {
        return new LlmChatResponse("", toolCalls);
    }

    public static LlmChatResponse ofTextAndToolCalls(String text, List<LlmToolCall> toolCalls) {
        return new LlmChatResponse(text, toolCalls);
    }

    public static LlmChatResponse empty() {
        return new LlmChatResponse("", List.of());
    }

    public boolean hasToolCalls() {
        return toolCalls != null && !toolCalls.isEmpty();
    }
}
