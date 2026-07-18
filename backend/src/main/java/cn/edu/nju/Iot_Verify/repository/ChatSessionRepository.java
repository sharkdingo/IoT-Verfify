package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import jakarta.persistence.LockModeType;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Lock;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;

import java.util.List;
import java.util.Optional;

public interface ChatSessionRepository extends JpaRepository<ChatSessionPo, String> {
    List<ChatSessionPo> findByUserIdOrderByUpdatedAtDesc(Long userId);
    Optional<ChatSessionPo> findByIdAndUserId(String id, Long userId);

    @Lock(LockModeType.PESSIMISTIC_WRITE)
    @Query("select chatSession from ChatSessionPo chatSession where chatSession.id = :id and chatSession.userId = :userId")
    Optional<ChatSessionPo> findByIdAndUserIdForUpdate(@Param("id") String id,
                                                       @Param("userId") Long userId);

    @Lock(LockModeType.PESSIMISTIC_WRITE)
    @Query("select chatSession from ChatSessionPo chatSession where chatSession.userId = :userId")
    List<ChatSessionPo> findByUserIdForUpdate(@Param("userId") Long userId);

    void deleteByUserId(Long userId);
}
