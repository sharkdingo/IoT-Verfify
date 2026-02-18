package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.util.List;

public interface ChatService {
    List<ChatSessionResponseDto> getUserSessions(Long userId);
    ChatSessionResponseDto createSession(Long userId);
    List<ChatMessageResponseDto> getHistory(Long userId, String sessionId);
    void deleteSession(Long userId, String sessionId);
    void processStreamChat(Long userId, String sessionId, String content, SseEmitter emitter);
}
