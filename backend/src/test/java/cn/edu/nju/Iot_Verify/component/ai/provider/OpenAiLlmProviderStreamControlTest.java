package cn.edu.nju.Iot_Verify.component.ai.provider;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatRequest;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.configure.LlmConfig;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import com.openai.client.OpenAIClient;
import com.openai.core.http.StreamResponse;
import com.openai.errors.OpenAIInvalidDataException;
import com.openai.models.chat.completions.ChatCompletionChunk;
import com.openai.models.chat.completions.ChatCompletionCreateParams;
import com.openai.services.blocking.ChatService;
import com.openai.services.blocking.chat.ChatCompletionService;
import org.junit.jupiter.api.Test;
import org.springframework.test.util.ReflectionTestUtils;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

/**
 * Verifies that {@link OpenAiLlmProvider#streamChat} honors the cooperative stop signal and
 * stops consuming further chunks — the behavior previously covered by the ArkAiClient stream
 * test, now against the OpenAI SDK adapter.
 */
class OpenAiLlmProviderStreamControlTest {

    @Test
    @SuppressWarnings("unchecked")
    void streamChat_withStopSignal_shouldStopConsumingFurtherChunks() {
        OpenAIClient client = mock(OpenAIClient.class);
        ChatService chatService = mock(ChatService.class);
        ChatCompletionService completions = mock(ChatCompletionService.class);
        StreamResponse<ChatCompletionChunk> streamResponse = mock(StreamResponse.class);

        when(client.chat()).thenReturn(chatService);
        when(chatService.completions()).thenReturn(completions);
        when(completions.createStreaming(any(ChatCompletionCreateParams.class))).thenReturn(streamResponse);
        when(streamResponse.stream()).thenReturn(List.of(chunk("A"), chunk("B"), chunk("C")).stream());

        LlmConfig config = new LlmConfig();
        config.setModel("mock-model");
        OpenAiLlmProvider provider = new OpenAiLlmProvider(config);
        ReflectionTestUtils.setField(provider, "client", client);

        List<String> outputs = new ArrayList<>();
        AtomicInteger stopChecks = new AtomicInteger(0);
        LlmChatRequest request = LlmChatRequest.builder()
                .messages(List.of(LlmMessage.user("hello")))
                .build();

        provider.streamChat(request, outputs::add, () -> stopChecks.incrementAndGet() > 1);

        // stop returns true on the 2nd check → only the first chunk is emitted
        assertEquals(List.of("A"), outputs);
    }

    @Test
    @SuppressWarnings("unchecked")
    void streamChat_whenSdkParsingFails_shouldPropagateServiceUnavailable() {
        OpenAIClient client = mock(OpenAIClient.class);
        ChatService chatService = mock(ChatService.class);
        ChatCompletionService completions = mock(ChatCompletionService.class);
        StreamResponse<ChatCompletionChunk> streamResponse = mock(StreamResponse.class);

        when(client.chat()).thenReturn(chatService);
        when(chatService.completions()).thenReturn(completions);
        when(completions.createStreaming(any(ChatCompletionCreateParams.class))).thenReturn(streamResponse);
        when(streamResponse.stream()).thenThrow(new OpenAIInvalidDataException("Invalid UTF-8 middle byte 0xe3"));

        LlmConfig config = new LlmConfig();
        config.setModel("mock-model");
        OpenAiLlmProvider provider = new OpenAiLlmProvider(config);
        ReflectionTestUtils.setField(provider, "client", client);

        LlmChatRequest request = LlmChatRequest.builder()
                .messages(List.of(LlmMessage.user("hello")))
                .build();

        assertThrows(ServiceUnavailableException.class,
                () -> provider.streamChat(request, ignored -> { }, () -> false));
    }

    private static ChatCompletionChunk chunk(String text) {
        ChatCompletionChunk.Choice choice = ChatCompletionChunk.Choice.builder()
                .delta(ChatCompletionChunk.Choice.Delta.builder().content(text).build())
                .finishReason(java.util.Optional.empty())
                .index(0L)
                .build();
        return ChatCompletionChunk.builder()
                .id("chunk_" + text)
                .addChoice(choice)
                .created(0L)
                .model("mock-model")
                .build();
    }
}
