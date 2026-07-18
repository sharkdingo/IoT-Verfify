package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.component.ai.state.AiSessionStateStore;
import cn.edu.nju.Iot_Verify.po.AiSessionStatePo;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;
import org.springframework.transaction.annotation.Transactional;

import java.time.Instant;

public interface AiSessionStateRepository extends JpaRepository<AiSessionStatePo, String> {

    @Modifying
    @Transactional
    @Query("delete from AiSessionStatePo state where state.stateKey = :stateKey and state.version = :version")
    int deleteByStateKeyAndVersion(@Param("stateKey") String stateKey,
                                   @Param("version") long version);

    @Modifying
    @Transactional
    @Query("delete from AiSessionStatePo state where state.userId = :userId and state.sessionId = :sessionId and state.stateKind = :kind")
    int deleteState(@Param("userId") Long userId,
                    @Param("sessionId") String sessionId,
                    @Param("kind") AiSessionStateStore.Kind kind);

    @Modifying
    @Transactional
    @Query("delete from AiSessionStatePo state where state.userId = :userId and state.sessionId = :sessionId")
    int deleteSession(@Param("userId") Long userId,
                      @Param("sessionId") String sessionId);

    @Modifying
    @Transactional
    @Query("delete from AiSessionStatePo state where state.userId = :userId")
    int deleteUser(@Param("userId") Long userId);

    @Modifying
    @Transactional
    @Query("delete from AiSessionStatePo state where state.expiresAt <= :now")
    int deleteExpired(@Param("now") Instant now);
}
