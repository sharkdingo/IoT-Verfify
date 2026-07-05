package cn.edu.nju.Iot_Verify.component.ai.provider;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatRequest;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatResponse;

import java.util.function.BooleanSupplier;
import java.util.function.Consumer;

/**
 * Strategy interface for a chat LLM backend. Implementations adapt a concrete vendor SDK
 * (OpenAI-compatible endpoints, including relays/proxies configured via {@code llm.base-url})
 * to the provider-agnostic domain model in {@code component.ai.model}.
 *
 * <p>This is the single seam that isolates the rest of the application from any SDK: no code
 * outside a {@code LlmProvider} implementation imports a vendor type. Adding another backend
 * means adding one implementation — nothing else changes.
 *
 * <p>Implementations must translate transport/SDK failures into
 * {@link cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException} so callers stay
 * SDK-agnostic.
 */
public interface LlmProvider {

    /**
     * Blocking chat completion. Used by the tool-calling loop (with tools) and by one-shot
     * prompt completions (without tools).
     *
     * @param request messages + optional tools + optional generation params
     * @return the model's reply as text or tool-call requests; {@link LlmChatResponse#empty()}
     *         if the provider returned no choice
     */
    LlmChatResponse chat(LlmChatRequest request);

    /**
     * Streaming chat completion. Text deltas are delivered to {@code onDelta} as they arrive.
     * Streaming stops early (and the underlying HTTP stream is closed) as soon as
     * {@code shouldStop} returns true — used to abort promptly on client disconnect.
     *
     * @param request    messages + optional generation params (tools are ignored for streaming)
     * @param onDelta    consumer invoked per non-empty text delta
     * @param shouldStop cooperative cancellation signal, polled between chunks
     */
    void streamChat(LlmChatRequest request, Consumer<String> onDelta, BooleanSupplier shouldStop);
}
