package cn.edu.nju.Iot_Verify.component.ai.model;

import java.util.List;

/**
 * Provider-agnostic non-streaming chat-completion result.
 *
 * <p>A response may contain text, tool calls, or both:
 * <ul>
 *   <li>the model returned text → {@code text} is non-blank, {@code toolCalls} empty;</li>
 *   <li>the model requested tools → {@code toolCalls} is non-empty;</li>
 *   <li>ReAct-capable providers may attach an explicit safe summary separately from the
 *       assistant text. Raw hidden chain-of-thought is never represented here.</li>
 * </ul>
 * An empty/absent choice from the provider maps to {@link #empty()}.
 *
 * @param text      assistant text content (never null; empty when no visible summary was returned)
 * @param toolCalls        tool-call requests (never null; empty when the model replied with text)
 * @param reasoningSummary provider-declared user-safe reasoning summary (never null)
 */
public record LlmChatResponse(String text,
                              List<LlmToolCall> toolCalls,
                              String reasoningSummary) {

    public LlmChatResponse {
        text = text == null ? "" : text;
        toolCalls = toolCalls == null ? List.of() : List.copyOf(toolCalls);
        reasoningSummary = reasoningSummary == null ? "" : reasoningSummary;
    }

    public LlmChatResponse(String text, List<LlmToolCall> toolCalls) {
        this(text, toolCalls, "");
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
