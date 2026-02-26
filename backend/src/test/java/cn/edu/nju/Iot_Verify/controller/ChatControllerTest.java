package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.chat.ChatRequestDto;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.ChatService;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.util.concurrent.Executor;
import java.util.concurrent.RejectedExecutionException;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.any;
import static org.mockito.Mockito.doAnswer;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.eq;
import static org.mockito.Mockito.same;
import static org.mockito.Mockito.verify;

@ExtendWith(MockitoExtension.class)
class ChatControllerTest {

    @Mock
    private ChatService chatService;

    @Mock
    private Executor executor;

    private ChatController controller;

    @BeforeEach
    void setUp() {
        controller = new ChatController(chatService, executor);
    }

    @Test
    void chat_executorRejected_throwsServiceUnavailable() {
        ChatRequestDto request = request("s1", "hello");
        doThrow(new RejectedExecutionException("pool saturated"))
                .when(executor).execute(any(Runnable.class));

        ServiceUnavailableException ex = assertThrows(ServiceUnavailableException.class,
                () -> controller.chat(1L, request));

        assertTrue(ex.getMessage().contains("busy"));
    }

    @Test
    void chat_executorAccepted_dispatchesToChatService() {
        ChatRequestDto request = request("s1", "hello");
        doAnswer(invocation -> {
            Runnable runnable = invocation.getArgument(0, Runnable.class);
            runnable.run();
            return null;
        }).when(executor).execute(any(Runnable.class));

        SseEmitter emitter = controller.chat(1L, request);

        assertNotNull(emitter);
        verify(chatService).processStreamChat(eq(1L), eq("s1"), eq("hello"), same(emitter));
    }

    private static ChatRequestDto request(String sessionId, String content) {
        ChatRequestDto request = new ChatRequestDto();
        request.setSessionId(sessionId);
        request.setContent(content);
        return request;
    }
}
