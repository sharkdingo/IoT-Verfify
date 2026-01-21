package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import org.springframework.data.jpa.repository.JpaRepository;

import java.util.List;
import java.util.Optional;

public interface ChatSessionRepository extends JpaRepository<ChatSessionPo, String> {
    List<ChatSessionPo> findByUserIdOrderByUpdatedAtDesc(Long userId);
    Optional<ChatSessionPo> findByIdAndUserId(String id, Long userId);
}
