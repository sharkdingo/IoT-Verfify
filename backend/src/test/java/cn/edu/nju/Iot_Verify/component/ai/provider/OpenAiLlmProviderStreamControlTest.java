package cn.edu.nju.Iot_Verify.component.ai.provider;

import cn.edu.nju.Iot_Verify.component.ai.LlmRequestControl;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatRequest;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmChatResponse;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.configure.LlmConfig;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.testutil.LogCapture;
import com.openai.client.OpenAIClient;
import com.openai.client.OpenAIClientAsync;
import com.openai.core.http.StreamResponse;
import com.openai.errors.OpenAIInvalidDataException;
import com.openai.models.chat.completions.ChatCompletionChunk;
import com.openai.models.chat.completions.ChatCompletion;
import com.openai.models.chat.completions.ChatCompletionCreateParams;
import com.openai.services.blocking.ChatService;
import com.openai.services.blocking.chat.ChatCompletionService;
import com.openai.services.async.ChatServiceAsync;
import com.openai.services.async.chat.ChatCompletionServiceAsync;
import org.junit.jupiter.api.Test;
import org.springframework.test.util.ReflectionTestUtils;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Spliterators;
import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.StreamSupport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.doAnswer;
import static org.mockito.Mockito.atLeastOnce;
import static org.mockito.Mockito.verify;
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

    @Test
    @SuppressWarnings("unchecked")
    void streamChat_cancelledFailure_doesNotLogUpstreamExceptionMessage() {
        String sensitive = "private-upstream-response-never-log";
        OpenAIClient client = mock(OpenAIClient.class);
        ChatService chatService = mock(ChatService.class);
        ChatCompletionService completions = mock(ChatCompletionService.class);
        StreamResponse<ChatCompletionChunk> streamResponse = mock(StreamResponse.class);

        when(client.chat()).thenReturn(chatService);
        when(chatService.completions()).thenReturn(completions);
        when(completions.createStreaming(any(ChatCompletionCreateParams.class))).thenReturn(streamResponse);
        when(streamResponse.stream()).thenThrow(new OpenAIInvalidDataException(sensitive));

        try (LogCapture logs = LogCapture.forClass(OpenAiLlmProvider.class)) {
            provider(client).streamChat(request(), ignored -> { }, () -> true);

            assertFalse(logs.messages().stream().anyMatch(message -> message.contains(sensitive)));
        }
    }

    @Test
    @SuppressWarnings("unchecked")
    void streamChat_explicitCancellation_shouldCloseBlockedUpstreamStream() throws Exception {
        OpenAIClient client = mock(OpenAIClient.class);
        ChatService chatService = mock(ChatService.class);
        ChatCompletionService completions = mock(ChatCompletionService.class);
        StreamResponse<ChatCompletionChunk> streamResponse = mock(StreamResponse.class);
        CountDownLatch iteratorBlocked = new CountDownLatch(1);
        CountDownLatch streamClosed = new CountDownLatch(1);
        Iterator<ChatCompletionChunk> blockingIterator = new Iterator<>() {
            @Override
            public boolean hasNext() {
                iteratorBlocked.countDown();
                try {
                    streamClosed.await(2, TimeUnit.SECONDS);
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                }
                return false;
            }

            @Override
            public ChatCompletionChunk next() {
                throw new java.util.NoSuchElementException();
            }
        };

        when(client.chat()).thenReturn(chatService);
        when(chatService.completions()).thenReturn(completions);
        when(completions.createStreaming(any(ChatCompletionCreateParams.class))).thenReturn(streamResponse);
        when(streamResponse.stream()).thenReturn(StreamSupport.stream(
                Spliterators.spliteratorUnknownSize(blockingIterator, 0), false));
        doAnswer(ignored -> {
            streamClosed.countDown();
            return null;
        }).when(streamResponse).close();

        OpenAiLlmProvider provider = provider(client);
        LlmRequestControl control = new LlmRequestControl();
        LlmChatRequest request = request();
        CompletableFuture<Void> call = CompletableFuture.runAsync(() ->
                provider.streamChat(request, ignored -> { }, () -> false, control));

        org.junit.jupiter.api.Assertions.assertTrue(iteratorBlocked.await(1, TimeUnit.SECONDS));
        control.cancel();
        call.get(2, TimeUnit.SECONDS);

        verify(streamResponse, atLeastOnce()).close();
    }

    @Test
    void chat_explicitCancellation_shouldCancelPendingPlanningRequest() throws Exception {
        OpenAIClient client = mock(OpenAIClient.class);
        OpenAIClientAsync asyncClient = mock(OpenAIClientAsync.class);
        ChatServiceAsync chatService = mock(ChatServiceAsync.class);
        ChatCompletionServiceAsync completions = mock(ChatCompletionServiceAsync.class);
        CompletableFuture<ChatCompletion> pending = new CompletableFuture<>();
        CountDownLatch requestStarted = new CountDownLatch(1);

        when(client.async()).thenReturn(asyncClient);
        when(asyncClient.chat()).thenReturn(chatService);
        when(chatService.completions()).thenReturn(completions);
        when(completions.create(any(ChatCompletionCreateParams.class))).thenAnswer(ignored -> {
            requestStarted.countDown();
            return pending;
        });

        OpenAiLlmProvider provider = provider(client);
        LlmRequestControl control = new LlmRequestControl();
        CompletableFuture<LlmChatResponse> call = CompletableFuture.supplyAsync(() ->
                provider.chat(request(), control));

        org.junit.jupiter.api.Assertions.assertTrue(requestStarted.await(1, TimeUnit.SECONDS));
        control.cancel();
        LlmChatResponse response = call.get(2, TimeUnit.SECONDS);

        org.junit.jupiter.api.Assertions.assertTrue(pending.isCancelled());
        org.junit.jupiter.api.Assertions.assertFalse(response.hasToolCalls());
        assertEquals("", response.text());
    }

    private static OpenAiLlmProvider provider(OpenAIClient client) {
        LlmConfig config = new LlmConfig();
        config.setModel("mock-model");
        OpenAiLlmProvider provider = new OpenAiLlmProvider(config);
        ReflectionTestUtils.setField(provider, "client", client);
        return provider;
    }

    private static LlmChatRequest request() {
        return LlmChatRequest.builder()
                .messages(List.of(LlmMessage.user("hello")))
                .build();
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
