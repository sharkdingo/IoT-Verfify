package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatRequestDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionActivityDto;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.ChatService;
import jakarta.validation.Valid;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.validation.annotation.Validated;
import org.springframework.web.bind.annotation.*;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.util.List;
import java.util.UUID;
import java.util.concurrent.Executor;
import java.util.concurrent.RejectedExecutionException;

@Slf4j
@Validated
@RestController
@RequestMapping("/api/chat")
public class ChatController {

    private final ChatService chatService;
    private final Executor executor;
    private final long sseTimeoutMs;

    public ChatController(ChatService chatService,
                          @Qualifier("chatExecutor") Executor executor,
                          @Value("${chat.sse-timeout-ms:3600000}") long sseTimeoutMs) {
        this.chatService = chatService;
        this.executor = executor;
        this.sseTimeoutMs = sseTimeoutMs;
    }

    @GetMapping("/sessions")
    public Result<List<ChatSessionResponseDto>> getSessions(@CurrentUser Long userId) {
        return Result.success(chatService.getUserSessions(userId));
    }

    @PostMapping("/sessions")
    public Result<ChatSessionResponseDto> createSession(@CurrentUser Long userId) {
        return Result.success(chatService.createSession(userId));
    }

    @GetMapping("/sessions/{sessionId}/messages")
    public Result<List<ChatMessageResponseDto>> getMessages(@CurrentUser Long userId, @PathVariable String sessionId) {
        return Result.success(chatService.getHistory(userId, sessionId));
    }

    @PostMapping("/completions")
    public SseEmitter chat(@CurrentUser Long userId, @Valid @RequestBody ChatRequestDto request) {
        log.debug("Received chat request from userId={}, sessionId={}", userId, request.getSessionId());
        SseEmitter emitter = new SseEmitter(sseTimeoutMs);
        String turnId = request.getTurnId() == null || request.getTurnId().isBlank()
                ? UUID.randomUUID().toString()
                : request.getTurnId().trim();
        String executionId = chatService.beginStreamRequest(userId, request.getSessionId());
        try {
            executor.execute(() -> {
                try {
                    chatService.processStreamChat(
                            userId, request.getSessionId(), executionId, turnId, request.getContent(), emitter);
                } catch (Exception e) {
                    log.error("Error processing chat request for userId={}", userId, e);
                    emitter.completeWithError(e);
                } finally {
                    chatService.endStreamRequest(userId, request.getSessionId(), executionId);
                }
            });
        } catch (RejectedExecutionException e) {
            chatService.endStreamRequest(userId, request.getSessionId(), executionId);
            log.warn("Chat request rejected: executor is saturated, userId={}, sessionId={}", userId, request.getSessionId());
            throw new ServiceUnavailableException("Chat service is busy, please retry later", e);
        }
        return emitter;
    }

    @GetMapping("/sessions/{sessionId}/activity")
    public Result<ChatSessionActivityDto> getSessionActivity(
            @CurrentUser Long userId, @PathVariable String sessionId) {
        return Result.success(chatService.getSessionActivity(userId, sessionId));
    }

    @PostMapping("/sessions/{sessionId}/stop")
    public Result<Void> stopSession(
            @CurrentUser Long userId, @PathVariable String sessionId) {
        chatService.requestStreamStop(userId, sessionId);
        return Result.success();
    }

    @DeleteMapping("/sessions/{sessionId}")
    public Result<Void> deleteSession(@CurrentUser Long userId, @PathVariable String sessionId) {
        log.debug("Deleting session: userId={}, sessionId={}", userId, sessionId);
        chatService.deleteSession(userId, sessionId);
        return Result.success();
    }
}
