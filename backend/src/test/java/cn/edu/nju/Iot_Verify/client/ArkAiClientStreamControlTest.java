package cn.edu.nju.Iot_Verify.client;

import cn.edu.nju.Iot_Verify.configure.ArkAiConfig;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionChoice;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionChunk;
import com.volcengine.ark.runtime.model.completion.chat.ChatCompletionRequest;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessage;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessageRole;
import com.volcengine.ark.runtime.service.ArkService;
import io.reactivex.Flowable;
import org.junit.jupiter.api.Test;
import org.springframework.test.util.ReflectionTestUtils;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

class ArkAiClientStreamControlTest {

    @Test
    void streamChat_withStopSignal_shouldStopConsumingFurtherChunks() {
        ArkService arkService = mock(ArkService.class);
        when(arkService.streamChatCompletion(any(ChatCompletionRequest.class)))
                .thenReturn(Flowable.just(chunk("A"), chunk("B"), chunk("C")));

        ArkAiConfig arkConfig = new ArkAiConfig();
        arkConfig.setModelId("mock-model");
        ArkAiClient client = new ArkAiClient(arkConfig, new com.fasterxml.jackson.databind.ObjectMapper());
        ReflectionTestUtils.setField(client, "arkService", arkService);

        List<String> outputs = new ArrayList<>();
        AtomicInteger stopChecks = new AtomicInteger(0);
        client.streamChat(
                List.of(ChatMessage.builder().role(ChatMessageRole.USER).content("hello").build()),
                outputs::add,
                () -> stopChecks.incrementAndGet() > 1
        );

        assertEquals(List.of("A"), outputs);
    }

    private static ChatCompletionChunk chunk(String text) {
        ChatCompletionChoice choice = new ChatCompletionChoice();
        choice.setMessage(ChatMessage.builder()
                .role(ChatMessageRole.ASSISTANT)
                .content(text)
                .build());

        ChatCompletionChunk chunk = new ChatCompletionChunk();
        chunk.setChoices(List.of(choice));
        return chunk;
    }
}
