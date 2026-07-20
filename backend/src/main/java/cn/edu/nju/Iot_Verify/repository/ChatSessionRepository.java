package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import jakarta.persistence.LockModeType;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Lock;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;
import org.springframework.transaction.annotation.Transactional;

import java.time.LocalDateTime;
import java.util.List;
import java.util.Optional;

public interface ChatSessionRepository extends JpaRepository<ChatSessionPo, String>, DatabaseClockRepository {

    List<ChatSessionPo> findByUserIdOrderByUpdatedAtDesc(Long userId);
    Optional<ChatSessionPo> findByIdAndUserId(String id, Long userId);

    @Lock(LockModeType.PESSIMISTIC_WRITE)
    @Query("select chatSession from ChatSessionPo chatSession where chatSession.id = :id and chatSession.userId = :userId")
    Optional<ChatSessionPo> findByIdAndUserIdForUpdate(@Param("id") String id,
                                                       @Param("userId") Long userId);

    @Lock(LockModeType.PESSIMISTIC_WRITE)
    @Query("select chatSession from ChatSessionPo chatSession where chatSession.userId = :userId")
    List<ChatSessionPo> findByUserIdForUpdate(@Param("userId") Long userId);

    @Modifying(clearAutomatically = true, flushAutomatically = true)
    @Transactional
    @Query("""
            update ChatSessionPo chatSession
               set chatSession.activeExecutionExpiresAt = :expiresAt
             where chatSession.id = :sessionId
               and chatSession.userId = :userId
               and chatSession.activeExecutionId = :executionId
               and chatSession.activeExecutionExpiresAt > :now
            """)
    int renewActiveExecutionLease(@Param("sessionId") String sessionId,
                                  @Param("userId") Long userId,
                                  @Param("executionId") String executionId,
                                  @Param("now") LocalDateTime now,
                                  @Param("expiresAt") LocalDateTime expiresAt);

    @Modifying(clearAutomatically = true, flushAutomatically = true)
    @Transactional
    @Query("""
            update ChatSessionPo chatSession
               set chatSession.activeExecutionId = null,
                   chatSession.activeExecutionExpiresAt = null,
                   chatSession.executionStopRequested = false,
                   chatSession.executionUserStopRequested = false
             where chatSession.activeExecutionId is not null
               and (chatSession.activeExecutionExpiresAt is null
                    or chatSession.activeExecutionExpiresAt <= :now)
            """)
    int clearExpiredExecutionLeases(@Param("now") LocalDateTime now);

    void deleteByUserId(Long userId);
}
