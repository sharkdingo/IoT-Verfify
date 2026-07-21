package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.chat.ChatMessageResponseDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatHistoryPageDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatConfirmationCommandDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatPendingConfirmationDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionActivityDto;
import cn.edu.nju.Iot_Verify.dto.chat.ChatSessionResponseDto;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.util.List;

public interface ChatService {
    List<ChatSessionResponseDto> getUserSessions(Long userId);
    ChatSessionResponseDto createSession(Long userId);
    List<ChatMessageResponseDto> getHistory(Long userId, String sessionId);
    ChatHistoryPageDto getHistoryPage(Long userId, String sessionId, Long beforeId, int limit);
    void deleteSession(Long userId, String sessionId);
    String beginStreamRequest(Long userId, String sessionId);
    void endStreamRequest(Long userId, String sessionId, String executionId);
    void requestStreamStop(Long userId, String sessionId);
    ChatSessionActivityDto getSessionActivity(Long userId, String sessionId);
    ChatPendingConfirmationDto getPendingConfirmation(Long userId, String sessionId);
    default void processStreamChat(Long userId, String sessionId, String executionId,
                                   String turnId, String content, SseEmitter emitter) {
        processStreamChat(userId, sessionId, executionId, turnId, content, null, emitter);
    }
    void processStreamChat(Long userId, String sessionId, String executionId,
                           String turnId, String content, ChatConfirmationCommandDto confirmation,
                           SseEmitter emitter);
}
