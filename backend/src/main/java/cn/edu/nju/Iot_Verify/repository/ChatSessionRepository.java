// src/main/java/cn/edu/nju/Iot_Verify/repository/ChatSessionRepository.java
package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import org.springframework.data.jpa.repository.JpaRepository;
import java.util.List;

public interface ChatSessionRepository extends JpaRepository<ChatSessionPo, String> {
    // 获取某用户的会话列表，按更新时间排序
    List<ChatSessionPo> findByUserIdOrderByUpdatedAtDesc(String userId);
}