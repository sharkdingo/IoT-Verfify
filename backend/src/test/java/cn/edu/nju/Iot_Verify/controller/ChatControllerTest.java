package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.chat.ChatRequestDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatStopRequestDto;
import cn.edu.nju.Iot_Verify.dto.chat.StreamResponseDto;
import cn.edu.nju.Iot_Verify.exception.ChatAdmissionOutcomeUnknownException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.service.ChatService;
import cn.edu.nju.Iot_Verify.service.UserOperationGuard;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.web.servlet.mvc.method.annotation.ResponseBodyEmitter;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.Executor;
import java.util.concurrent.RejectedExecutionException;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.any;
import static org.mockito.Mockito.doAnswer;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.eq;
import static org.mockito.Mockito.same;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.Mockito.mock;

@ExtendWith(MockitoExtension.class)
class ChatControllerTest {

    @Mock
    private ChatService chatService;

    @Mock
    private Executor executor;

    @Mock
    private UserOperationGuard userOperationGuard;

    private ChatController controller;

    @BeforeEach
    void setUp() {
        controller = new ChatController(chatService, executor, userOperationGuard, 600000L);
    }

    @Test
    void chat_executorRejected_throwsServiceUnavailable() {
        ChatRequestDto request = request("s1", "hello");
        when(userOperationGuard.acquire(any(), any(), anyInt(), any()))
                .thenReturn(org.mockito.Mockito.mock(UserOperationGuard.Lease.class));
        when(chatService.beginStreamRequest(1L, "s1", "turn-s1", "hello"))
                .thenReturn("execution-s1");
        doThrow(new RejectedExecutionException("pool saturated"))
                .when(executor).execute(any(Runnable.class));

        ServiceUnavailableException ex = assertThrows(ServiceUnavailableException.class,
                () -> controller.chat(1L, request));

        assertTrue(ex.getMessage().contains("busy"));
        verify(chatService).abortUndispatched(1L, "s1", "execution-s1", "turn-s1");
        verify(chatService, org.mockito.Mockito.never())
                .endStreamRequest(1L, "s1", "execution-s1");
    }

    @Test
    void chat_executorAccepted_dispatchesToChatService() {
        ChatRequestDto request = request("s1", "hello");
        when(userOperationGuard.acquire(any(), any(), anyInt(), any()))
                .thenReturn(org.mockito.Mockito.mock(UserOperationGuard.Lease.class));
        when(chatService.beginStreamRequest(1L, "s1", "turn-s1", "hello"))
                .thenReturn("execution-s1");
        doAnswer(invocation -> {
            Runnable runnable = invocation.getArgument(0, Runnable.class);
            runnable.run();
            return null;
        }).when(executor).execute(any(Runnable.class));

        SseEmitter emitter = controller.chat(1L, request);

        assertNotNull(emitter);
        verify(chatService).processStreamChat(
                eq(1L), eq("s1"), eq("execution-s1"), eq("turn-s1"), eq("hello"), eq(null), same(emitter));
        verify(chatService).endStreamRequest(1L, "s1", "execution-s1");
    }

    @Test
    void chat_executorRejectedWithUnknownRollback_returnsAcceptedReconciliationStream() {
        ChatRequestDto request = request("s1", "hello");
        UserOperationGuard.Lease userLease = mock(UserOperationGuard.Lease.class);
        when(userOperationGuard.acquire(any(), any(), anyInt(), any())).thenReturn(userLease);
        when(chatService.beginStreamRequest(1L, "s1", "turn-s1", "hello"))
                .thenReturn("execution-s1");
        doThrow(new RejectedExecutionException("pool saturated"))
                .when(executor).execute(any(Runnable.class));
        doThrow(new IllegalStateException("database unavailable"))
                .when(chatService).abortUndispatched(
                        1L, "s1", "execution-s1", "turn-s1");

        SseEmitter emitter = controller.chat(1L, request);

        assertNotNull(emitter);
        verify(userLease).close();
        verify(chatService, org.mockito.Mockito.never())
                .endStreamRequest(1L, "s1", "execution-s1");
    }

    @Test
    void chat_admissionSelfCheckWithUnknownRollback_returnsReconciliationStream() {
        ChatRequestDto request = request("s1", "hello");
        UserOperationGuard.Lease userLease = mock(UserOperationGuard.Lease.class);
        when(userOperationGuard.acquire(any(), any(), anyInt(), any())).thenReturn(userLease);
        when(chatService.beginStreamRequest(1L, "s1", "turn-s1", "hello"))
                .thenThrow(new ChatAdmissionOutcomeUnknownException(
                        "rollback unknown", new IllegalStateException("database unavailable")));

        SseEmitter emitter = controller.chat(1L, request);

        assertNotNull(emitter);
        verify(userLease).close();
        verify(executor, org.mockito.Mockito.never()).execute(any(Runnable.class));
    }

    @Test
    void admissionOutcomeUnknown_emitsOnlyAnErrorFrameAndCompletes() throws IOException {
        SseEmitter emitter = mock(SseEmitter.class);
        List<StreamResponseDto> frames = new ArrayList<>();
        doAnswer(invocation -> {
            SseEmitter.SseEventBuilder event =
                    invocation.getArgument(0, SseEmitter.SseEventBuilder.class);
            for (ResponseBodyEmitter.DataWithMediaType item : event.build()) {
                if (item.getData() instanceof StreamResponseDto frame) frames.add(frame);
            }
            return null;
        }).when(emitter).send(any(SseEmitter.SseEventBuilder.class));

        controller.completeAdmissionOutcomeUnknown(emitter, "hello");

        assertEquals(1, frames.size());
        StreamResponseDto frame = frames.get(0);
        assertNull(frame.getContent());
        assertTrue(frame.getError().contains("could not be confirmed"));
        assertNull(frame.getCommand());
        assertNull(frame.getProgress());
        assertNull(frame.getTerminal());
        verify(emitter).complete();
    }

    @Test
    void chat_executionCleanupFailureStillReleasesTheUserAdmissionLease() {
        ChatRequestDto request = request("s1", "hello");
        UserOperationGuard.Lease userLease = mock(UserOperationGuard.Lease.class);
        when(userOperationGuard.acquire(any(), any(), anyInt(), any())).thenReturn(userLease);
        when(chatService.beginStreamRequest(1L, "s1", "turn-s1", "hello"))
                .thenReturn("execution-s1");
        doThrow(new IllegalStateException("database unavailable"))
                .when(chatService).endStreamRequest(1L, "s1", "execution-s1");
        doAnswer(invocation -> {
            invocation.getArgument(0, Runnable.class).run();
            return null;
        }).when(executor).execute(any(Runnable.class));

        assertNotNull(controller.chat(1L, request));

        verify(userLease).close();
    }

    @Test
    void chat_workerLeaseAttachmentFailure_rollsBackThePersistedAdmission() {
        ChatRequestDto request = request("s1", "hello");
        UserOperationGuard.Lease userLease = mock(UserOperationGuard.Lease.class);
        when(userOperationGuard.acquire(any(), any(), anyInt(), any())).thenReturn(userLease);
        when(chatService.beginStreamRequest(1L, "s1", "turn-s1", "hello"))
                .thenReturn("execution-s1");
        doThrow(new IllegalStateException("lease lost"))
                .when(userLease).attachCurrentThread();
        doAnswer(invocation -> {
            invocation.getArgument(0, Runnable.class).run();
            return null;
        }).when(executor).execute(any(Runnable.class));

        assertNotNull(controller.chat(1L, request));

        verify(chatService).abortUndispatched(1L, "s1", "execution-s1", "turn-s1");
        verify(chatService, org.mockito.Mockito.never()).processStreamChat(
                any(), any(), any(), any(), any(), any(), any());
        verify(chatService, org.mockito.Mockito.never())
                .endStreamRequest(1L, "s1", "execution-s1");
        verify(userLease).close();
    }

    @Test
    void stopSession_delegatesExplicitStopToOwnedSession() {
        ChatStopRequestDto request = new ChatStopRequestDto();
        request.setTurnId("turn-s1");

        controller.stopSession(1L, "s1", request);

        verify(chatService).requestStreamStop(1L, "s1", "turn-s1");
    }

    @Test
    void stopSession_allowsReattachedExecutionWithoutKnownTurnId() {
        ChatStopRequestDto request = new ChatStopRequestDto();

        controller.stopSession(1L, "s1", request);

        verify(chatService).requestStreamStop(1L, "s1", null);
    }

    private static ChatRequestDto request(String sessionId, String content) {
        ChatRequestDto request = new ChatRequestDto();
        request.setSessionId(sessionId);
        request.setContent(content);
        request.setTurnId("turn-" + sessionId);
        return request;
    }
}
