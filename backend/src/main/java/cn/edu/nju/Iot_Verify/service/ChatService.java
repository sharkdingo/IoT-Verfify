package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import org.springframework.web.servlet.mvc.method.annotation.SseEmitter;

import java.util.List;

public interface ChatService {

    /**
     * 获取指定用户的会话列表
     */
    List<ChatSessionPo> getUserSessions(String userId);

    /**
     * 创建新的会话
     */
    ChatSessionPo createSession(String userId);

    /**
     * 获取指定会话的历史消息
     */
    List<ChatMessagePo> getHistory(String sessionId);

    /**
     * 删除会话及其消息
     */
    void deleteSession(String sessionId);

    /**
     * 核心流式对话处理
     * @param sessionId 会话ID
     * @param content 用户输入内容
     * @param emitter SSE 发射器
     */
    void processStreamChat(String sessionId, String content, SseEmitter emitter);
}