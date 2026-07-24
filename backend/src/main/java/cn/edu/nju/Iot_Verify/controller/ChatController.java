package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.chat.ChatHistoryPageDto;
import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import cn.edu.nju.Iot_Verify.dto.chat.ChatRequestDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionActivityDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatPendingConfirmationDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatStopRequestDto;
import cn.edu.nju.Iot_Verify.dto.chat.StreamResponseDto;
import cn.edu.nju.Iot_Verify.exception.ChatAdmissionOutcomeUnknownException;
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
import org.springframework.http.MediaType;
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
            executionId = chatService.beginStreamRequest(
                    userId, request.getSessionId(), turnId, request.getContent());
        } catch (ChatAdmissionOutcomeUnknownException e) {
            userLease.close();
            log.error("Chat admission rollback outcome is unknown: userId={}, sessionId={}",
                    userId, request.getSessionId(), e);
            completeAdmissionOutcomeUnknown(emitter, request.getContent());
            return emitter;
        } catch (RuntimeException e) {
            userLease.close();
            throw e;
        }
        try {
            executor.execute(() -> {
                boolean userLeaseAttached = false;
                try {
                    userLease.attachCurrentThread();
                    userLeaseAttached = true;
                    chatService.processStreamChat(
                            userId, request.getSessionId(), executionId, turnId, request.getContent(),
                            request.getConfirmation(), emitter);
                    userLease.requireActive();
                } catch (Exception e) {
                    if (!userLeaseAttached) {
                        if (!abortUndispatchedRequest(
                                userId, request.getSessionId(), executionId, turnId, userLease)) {
                            completeAdmissionOutcomeUnknown(emitter, request.getContent());
                        } else {
                            emitter.completeWithError(e);
                        }
                        return;
                    }
                    log.error("Error processing chat request for userId={}", userId, e);
                    emitter.completeWithError(e);
                } finally {
                    if (userLeaseAttached) {
                        cleanupStreamRequest(userId, request.getSessionId(), executionId, userLease);
                    }
                }
            });
        } catch (RejectedExecutionException e) {
            if (!abortUndispatchedRequest(
                    userId, request.getSessionId(), executionId, turnId, userLease)) {
                completeAdmissionOutcomeUnknown(emitter, request.getContent());
                return emitter;
            }
            log.warn("Chat request rejected: executor is saturated, userId={}, sessionId={}", userId, request.getSessionId());
            throw new ServiceUnavailableException("Chat service is busy, please retry later", e);
        } catch (RuntimeException e) {
            if (!abortUndispatchedRequest(
                    userId, request.getSessionId(), executionId, turnId, userLease)) {
                completeAdmissionOutcomeUnknown(emitter, request.getContent());
                return emitter;
            }
            throw e;
        }
        return emitter;
    }

    private boolean abortUndispatchedRequest(Long userId,
                                             String sessionId,
                                             String executionId,
                                             String turnId,
                                             UserOperationGuard.Lease userLease) {
        try {
            chatService.abortUndispatched(userId, sessionId, executionId, turnId);
            return true;
        } catch (RuntimeException rollbackFailure) {
            log.error("Could not confirm rollback of an undispatched chat request: "
                            + "userId={}, sessionId={}, executionId={}",
                    userId, sessionId, executionId, rollbackFailure);
            return false;
        } finally {
            userLease.close();
        }
    }

    void completeAdmissionOutcomeUnknown(SseEmitter emitter, String content) {
        String message = content != null && content.codePoints().anyMatch(codePoint ->
                Character.UnicodeScript.of(codePoint) == Character.UnicodeScript.HAN)
                ? "请求未能确认开始执行，且已保存请求的回滚结果无法确认。"
                    + "请等待会话空闲后刷新历史和画布，不要立即重试。"
                : "The request was not confirmed as started, and rollback of its saved "
                    + "admission could not be confirmed. Wait for the session to become idle, then refresh "
                    + "history and the Board before retrying.";
        try {
            emitter.send(SseEmitter.event().data(StreamResponseDto.error(message), MediaType.APPLICATION_JSON));
        } catch (Exception sendFailure) {
            log.warn("Could not send the chat admission-outcome warning: {}", sendFailure.toString());
        } finally {
            emitter.complete();
        }
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
            @PathVariable @Size(max = 64, message = "Session ID must not exceed 64 characters") String sessionId,
            @Valid @RequestBody ChatStopRequestDto request) {
        chatService.requestStreamStop(userId, sessionId, request.getTurnId());
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
