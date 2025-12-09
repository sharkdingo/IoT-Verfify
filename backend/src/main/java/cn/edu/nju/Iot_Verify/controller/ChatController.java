package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.ChatRequestDto;
import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.service.ChatService;
import lombok.RequiredArgsConstructor;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.web.bind.annotation.*;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.util.List;
import java.util.concurrent.Executor;


@RestController
@RequestMapping("/api/chat")
//@RequiredArgsConstructor
public class ChatController {

    private final ChatService chatService;
    private final Executor executor;

    public ChatController(ChatService chatService,
                          @Qualifier("chatExecutor") Executor executor) {
        this.chatService = chatService;
        this.executor = executor;
    }

    @GetMapping("/sessions")
    public Result<List<ChatSessionPo>> getSessions(@RequestParam String userId) {
        return Result.success(chatService.getUserSessions(userId));
    }

    @PostMapping("/sessions")
    public Result<ChatSessionPo> createSession(@RequestParam String userId) {
        return Result.success(chatService.createSession(userId));
    }

    @GetMapping("/sessions/{sessionId}/messages")
    public Result<List<ChatMessagePo>> getMessages(@PathVariable String sessionId) {
        return Result.success(chatService.getHistory(sessionId));
    }

    @PostMapping("/completions")
    public SseEmitter chat(@RequestBody ChatRequestDto request) {
        // 设置 5 分钟超时
        SseEmitter emitter = new SseEmitter(5 * 60 * 1000L);

        executor.execute(() -> {
            try {
                chatService.processStreamChat(request.getSessionId(), request.getContent(), emitter);
            } catch (Exception e) {
                // 如果是拒绝策略抛出的异常，这里也能捕获
                emitter.completeWithError(e);
            }
        });
        return emitter;
    }

    @DeleteMapping("/sessions/{sessionId}")
    public Result<Void> deleteSession(@PathVariable String sessionId) {
        chatService.deleteSession(sessionId);
        return Result.success(null);
    }
}

