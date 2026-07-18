package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionActivityDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.util.List;

public interface ChatService {
    List<ChatSessionResponseDto> getUserSessions(Long userId);
    ChatSessionResponseDto createSession(Long userId);
    List<ChatMessageResponseDto> getHistory(Long userId, String sessionId);
    void deleteSession(Long userId, String sessionId);
    void beginStreamRequest(Long userId, String sessionId);
    void endStreamRequest(Long userId, String sessionId);
    void requestStreamStop(Long userId, String sessionId);
    ChatSessionActivityDto getSessionActivity(Long userId, String sessionId);
    void processStreamChat(Long userId, String sessionId, String turnId, String content, SseEmitter emitter);
}
