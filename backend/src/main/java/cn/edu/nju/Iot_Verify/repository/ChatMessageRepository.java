// src/main/java/cn/edu/nju/Iot_Verify/repository/ChatMessageRepository.java
package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.List;

public interface ChatMessageRepository extends JpaRepository<ChatMessagePo, Long> {
    // Full session history for frontend timeline.
    List<ChatMessagePo> findBySessionIdOrderByCreatedAtAsc(String sessionId);

    // Recent message windows for AI context.
    List<ChatMessagePo> findTop10BySessionIdOrderByCreatedAtDesc(String sessionId);
    List<ChatMessagePo> findTop80BySessionIdOrderByCreatedAtDesc(String sessionId);

    void deleteBySessionId(String sessionId);
}
