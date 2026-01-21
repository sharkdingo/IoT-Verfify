package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.ChatRequestDto;
import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.ChatService;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.web.bind.annotation.*;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.util.List;
import java.util.concurrent.Executor;

@RestController
@RequestMapping("/api/chat")
public class ChatController {

    private final ChatService chatService;
    private final Executor executor;

    public ChatController(ChatService chatService,
                          @Qualifier("chatExecutor") Executor executor) {
        this.chatService = chatService;
        this.executor = executor;
    }

    @GetMapping("/sessions")
    public Result<List<ChatSessionPo>> getSessions(@CurrentUser Long userId) {
        return Result.success(chatService.getUserSessions(userId));
    }

    @PostMapping("/sessions")
    public Result<ChatSessionPo> createSession(@CurrentUser Long userId) {
        return Result.success(chatService.createSession(userId));
    }

    @GetMapping("/sessions/{sessionId}/messages")
    public Result<List<ChatMessagePo>> getMessages(@CurrentUser Long userId, @PathVariable String sessionId) {
        return Result.success(chatService.getHistory(userId, sessionId));
    }

    @PostMapping("/completions")
    public SseEmitter chat(@CurrentUser Long userId, @RequestBody ChatRequestDto request) {
        SseEmitter emitter = new SseEmitter(5 * 60 * 1000L);

        executor.execute(() -> {
            try {
                chatService.processStreamChat(userId, request.getSessionId(), request.getContent(), emitter);
            } catch (Exception e) {
                emitter.completeWithError(e);
            }
        });
        return emitter;
    }

    @DeleteMapping("/sessions/{sessionId}")
    public Result<Void> deleteSession(@CurrentUser Long userId, @PathVariable String sessionId) {
        chatService.deleteSession(userId, sessionId);
        return Result.success(null);
    }
}
