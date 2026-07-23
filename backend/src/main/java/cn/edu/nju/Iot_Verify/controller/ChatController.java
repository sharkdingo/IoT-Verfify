package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.chat.ChatHistoryPageDto;
import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import cn.edu.nju.Iot_Verify.dto.chat.ChatRequestDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionActivityDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatPendingConfirmationDto;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.ChatService;
import cn.edu.nju.Iot_Verify.service.UserOperationGuard;
import jakarta.validation.Valid;
import jakarta.validation.constraints.Positive;
import jakarta.validation.constraints.Size;
import jakarta.validation.constraints.Max;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.validation.annotation.Validated;
import org.springframework.web.bind.annotation.*;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.util.List;
import java.util.concurrent.Executor;
import java.util.concurrent.RejectedExecutionException;
import java.time.Duration;

@Slf4j
@Validated
@RestController
@RequestMapping("/api/chat")
public class ChatController {

    private final ChatService chatService;
    private final Executor executor;
    private final UserOperationGuard userOperationGuard;
    private final long sseTimeoutMs;

    public ChatController(ChatService chatService,
                          @Qualifier("chatExecutor") Executor executor,
                          UserOperationGuard userOperationGuard,
                          @Value("${chat.sse-timeout-ms:3600000}") long sseTimeoutMs) {
        this.chatService = chatService;
        this.executor = executor;
        this.userOperationGuard = userOperationGuard;
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
    public Result<ChatHistoryPageDto> getMessages(
            @CurrentUser Long userId,
            @PathVariable @Size(max = 64, message = "Session ID must not exceed 64 characters") String sessionId,
            @RequestParam(required = false) @Positive(message = "History cursor must be positive") Long beforeId,
            @RequestParam(required = false, defaultValue = "50")
            @Positive @Max(value = RequestLimits.MAX_CHAT_HISTORY_PAGE_SIZE,
                    message = "History page size must not exceed 100") Integer limit) {
        return Result.success(chatService.getHistoryPage(
                userId, sessionId, beforeId,
                limit == null ? RequestLimits.DEFAULT_CHAT_HISTORY_PAGE_SIZE : limit));
    }

    @PostMapping("/completions")
    public SseEmitter chat(@CurrentUser Long userId, @Valid @RequestBody ChatRequestDto request) {
        log.debug("Received chat request from userId={}, sessionId={}", userId, request.getSessionId());
        SseEmitter emitter = new SseEmitter(sseTimeoutMs);
        UserOperationGuard.Lease userLease = userOperationGuard.acquire(
                userId, UserOperationGuard.Kind.CHAT, 2, Duration.ofHours(2));
        String turnId = request.getTurnId().trim();
        String executionId;
        try {
            userLease.requireActive();
            executionId = chatService.beginStreamRequest(userId, request.getSessionId());
        } catch (RuntimeException e) {
            userLease.close();
            throw e;
        }
        try {
            executor.execute(() -> {
                try {
                    userLease.attachCurrentThread();
                    chatService.processStreamChat(
                            userId, request.getSessionId(), executionId, turnId, request.getContent(),
                            request.getConfirmation(), emitter);
                    userLease.requireActive();
                } catch (Exception e) {
                    log.error("Error processing chat request for userId={}", userId, e);
                    emitter.completeWithError(e);
                } finally {
                    cleanupStreamRequest(userId, request.getSessionId(), executionId, userLease);
                }
            });
        } catch (RejectedExecutionException e) {
            cleanupStreamRequest(userId, request.getSessionId(), executionId, userLease);
            log.warn("Chat request rejected: executor is saturated, userId={}, sessionId={}", userId, request.getSessionId());
            throw new ServiceUnavailableException("Chat service is busy, please retry later", e);
        } catch (RuntimeException e) {
            cleanupStreamRequest(userId, request.getSessionId(), executionId, userLease);
            throw e;
        }
        return emitter;
    }

    private void cleanupStreamRequest(Long userId,
                                      String sessionId,
                                      String executionId,
                                      UserOperationGuard.Lease userLease) {
        try {
            chatService.endStreamRequest(userId, sessionId, executionId);
        } catch (RuntimeException e) {
            log.error("Could not release chat execution state for userId={}, sessionId={}, executionId={}",
                    userId, sessionId, executionId, e);
        } finally {
            userLease.close();
        }
    }

    @GetMapping("/sessions/{sessionId}/activity")
    public Result<ChatSessionActivityDto> getSessionActivity(
            @CurrentUser Long userId,
            @PathVariable @Size(max = 64, message = "Session ID must not exceed 64 characters") String sessionId) {
        return Result.success(chatService.getSessionActivity(userId, sessionId));
    }

    @GetMapping("/sessions/{sessionId}/confirmation")
    public Result<ChatPendingConfirmationDto> getPendingConfirmation(
            @CurrentUser Long userId,
            @PathVariable @Size(max = 64, message = "Session ID must not exceed 64 characters") String sessionId) {
        return Result.success(chatService.getPendingConfirmation(userId, sessionId));
    }

    @PostMapping("/sessions/{sessionId}/stop")
    public Result<Void> stopSession(
            @CurrentUser Long userId,
            @PathVariable @Size(max = 64, message = "Session ID must not exceed 64 characters") String sessionId) {
        chatService.requestStreamStop(userId, sessionId);
        return Result.success();
    }

    @DeleteMapping("/sessions/{sessionId}")
    public Result<Void> deleteSession(
            @CurrentUser Long userId,
            @PathVariable @Size(max = 64, message = "Session ID must not exceed 64 characters") String sessionId) {
        log.debug("Deleting session: userId={}, sessionId={}", userId, sessionId);
        chatService.deleteSession(userId, sessionId);
        return Result.success();
    }
}
