package cn.edu.nju.Iot_Verify.component.ai;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatRequest;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatResponse;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolSpec;
import cn.edu.nju.Iot_Verify.component.ai.provider.LlmProvider;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Service;

import java.util.List;
import java.util.function.BooleanSupplier;
import java.util.function.Consumer;

/**
 * Facade the chat orchestration layer ({@code ChatServiceImpl}) talks to. Combines the
 * {@link LlmProvider} strategy with {@link LlmMessageCodec} so the orchestrator deals only
 * in {@link LlmMessage}/{@link LlmChatResponse} and never touches a provider SDK or the
 * persistence wire format directly.
 */
@Slf4j
@Service
@RequiredArgsConstructor
public class LlmChatService {

    private final LlmProvider llmProvider;
    private final LlmMessageCodec messageCodec;

    /** Reconstruct provider-agnostic messages from persisted chat rows. */
    public List<LlmMessage> toMessages(List<ChatMessagePo> history) {
        return messageCodec.toMessages(history);
    }

    /**
     * One tool-aware planning round. The chat service executes returned tool calls and ignores
     * final text here so the visible assistant reply can always be streamed afterward.
     */
    public LlmChatResponse chatWithTools(List<LlmMessage> messages, List<LlmToolSpec> tools) {
        LlmChatRequest request = LlmChatRequest.builder()
                .messages(messages)
                .tools(tools)
                .build();
        return llmProvider.chat(request, LlmRequestControlHolder.currentOrNew());
    }

    /**
     * Stream the visible assistant reply (no tools), forwarding text deltas to {@code onDelta}
     * until {@code shouldStop} signals cancellation.
     */
    public void streamReply(List<LlmMessage> messages, Consumer<String> onDelta, BooleanSupplier shouldStop) {
        LlmChatRequest request = LlmChatRequest.builder()
                .messages(messages)
                .build();
        llmProvider.streamChat(
                request, onDelta, shouldStop, LlmRequestControlHolder.currentOrNew());
    }
}
