// src/main/java/cn/edu/nju/Iot_Verify/repository/ChatMessageRepository.java
package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.domain.Pageable;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.transaction.annotation.Transactional;

import java.util.Collection;
import java.util.List;

public interface ChatMessageRepository extends JpaRepository<ChatMessagePo, Long> {
    // Full session history for frontend timeline.
    List<ChatMessagePo> findBySessionIdOrderByCreatedAtAsc(String sessionId);
    List<ChatMessagePo> findBySessionIdOrderByIdDesc(String sessionId, Pageable pageable);
    List<ChatMessagePo> findBySessionIdAndIdLessThanOrderByIdDesc(
            String sessionId, Long id, Pageable pageable);

    // Recent message window for AI context. The database id is the cross-instance order.
    List<ChatMessagePo> findTop80BySessionIdOrderByIdDesc(String sessionId);

    long countBySessionId(String sessionId);
    boolean existsBySessionIdAndTurnId(String sessionId, String turnId);
    boolean existsBySessionIdAndTurnIdAndExecutionIdAndRole(
            String sessionId, String turnId, String executionId, String role);

    @Modifying(flushAutomatically = true, clearAutomatically = true)
    @Transactional
    int deleteBySessionIdAndTurnIdAndExecutionIdAndRole(
            String sessionId, String turnId, String executionId, String role);

    void deleteBySessionId(String sessionId);
    void deleteBySessionIdIn(Collection<String> sessionIds);
}
