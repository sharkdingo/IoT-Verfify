package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.util.List;

public interface ChatService {
    List<ChatSessionPo> getUserSessions(Long userId);
    ChatSessionPo createSession(Long userId);
    List<ChatMessagePo> getHistory(Long userId, String sessionId);
    void deleteSession(Long userId, String sessionId);
    void processStreamChat(Long userId, String sessionId, String content, SseEmitter emitter);
}
