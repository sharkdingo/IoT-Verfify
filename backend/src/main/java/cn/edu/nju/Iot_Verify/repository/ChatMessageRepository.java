// src/main/java/cn/edu/nju/Iot_Verify/repository/ChatMessageRepository.java
package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import org.springframework.data.jpa.repository.JpaRepository;
import java.util.List;

public interface ChatMessageRepository extends JpaRepository<ChatMessagePo, Long> {
    // 1. 获取某会话的所有消息 (用于前端展示历史)
    List<ChatMessagePo> findBySessionIdOrderByCreatedAtAsc(String sessionId);

    // 2. 获取最近 N 条消息 (用于喂给 AI 做上下文) - 倒序查
    List<ChatMessagePo> findTop10BySessionIdOrderByCreatedAtDesc(String sessionId);

    void deleteBySessionId(String sessionId);
}