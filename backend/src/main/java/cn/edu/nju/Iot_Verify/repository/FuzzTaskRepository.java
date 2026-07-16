package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzOutcome;
import cn.edu.nju.Iot_Verify.po.FuzzTaskPo;
import cn.edu.nju.Iot_Verify.dto.model.TaskProgressStage;
import cn.edu.nju.Iot_Verify.repository.projection.FuzzTaskSummaryProjection;
import cn.edu.nju.Iot_Verify.repository.projection.FuzzTaskProgressProjection;
import org.springframework.data.domain.Pageable;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;
import org.springframework.stereotype.Repository;
import org.springframework.transaction.annotation.Transactional;

import java.time.LocalDateTime;
import java.util.List;
import java.util.Optional;

@Repository
public interface FuzzTaskRepository extends JpaRepository<FuzzTaskPo, Long> {

    @Query(value = "SELECT CURRENT_TIMESTAMP", nativeQuery = true)
    LocalDateTime currentDatabaseTime();

    Optional<FuzzTaskPo> findByIdAndUserId(Long id, Long userId);

    Optional<FuzzTaskSummaryProjection> findSummaryByIdAndUserId(Long id, Long userId);

    Optional<FuzzTaskPo> findByIdAndUserIdAndStatus(
            Long id, Long userId, FuzzTaskPo.TaskStatus status);

    @Query("SELECT t.status FROM FuzzTaskPo t WHERE t.id = :taskId")
    Optional<FuzzTaskPo.TaskStatus> findStatusById(@Param("taskId") Long taskId);

    @Query("SELECT t.progress AS progress, t.status AS status FROM FuzzTaskPo t "
         + "WHERE t.id = :taskId AND t.userId = :userId")
    Optional<FuzzTaskProgressProjection> findProgressByIdAndUserId(
            @Param("taskId") Long taskId, @Param("userId") Long userId);

    List<FuzzTaskPo> findByUserIdAndStatus(Long userId, FuzzTaskPo.TaskStatus status);

    long countByUserId(Long userId);

    long countByUserIdAndStatusIn(Long userId, List<FuzzTaskPo.TaskStatus> statuses);

    @Query("SELECT t.id FROM FuzzTaskPo t WHERE t.userId = :userId AND t.status = :status")
    List<Long> findIdsByUserIdAndStatus(@Param("userId") Long userId,
                                        @Param("status") FuzzTaskPo.TaskStatus status);

    List<FuzzTaskPo> findByUserIdAndStatusNotOrderByCreatedAtDescIdDesc(
            Long userId, FuzzTaskPo.TaskStatus status, Pageable pageable);

    List<FuzzTaskSummaryProjection> findSummaryByUserIdAndStatusNotOrderByCreatedAtDescIdDesc(
            Long userId, FuzzTaskPo.TaskStatus status, Pageable pageable);

    List<FuzzTaskPo> findByUserIdAndStatusNotAndIdNotInOrderByCreatedAtDescIdDesc(
            Long userId, FuzzTaskPo.TaskStatus status, List<Long> excludedIds, Pageable pageable);

    List<FuzzTaskSummaryProjection> findSummaryByUserIdAndStatusNotAndIdNotInOrderByCreatedAtDescIdDesc(
            Long userId, FuzzTaskPo.TaskStatus status, List<Long> excludedIds, Pageable pageable);

    List<FuzzTaskPo> findByUserIdAndStatusOrderByCreatedAtDescIdDesc(
            Long userId, FuzzTaskPo.TaskStatus status, Pageable pageable);

    List<FuzzTaskSummaryProjection> findSummaryByUserIdAndStatusOrderByCreatedAtDescIdDesc(
            Long userId, FuzzTaskPo.TaskStatus status, Pageable pageable);

    @Transactional
    @Modifying(clearAutomatically = true, flushAutomatically = true)
    @Query("DELETE FROM FuzzTaskPo t WHERE t.userId = :userId")
    int deleteByUserId(@Param("userId") Long userId);

    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("DELETE FROM FuzzTaskPo t WHERE t.id = :taskId AND t.userId = :userId "
         + "AND t.workerId = :workerId AND t.status = :pending")
    int deleteUndispatchedTask(@Param("taskId") Long taskId,
                               @Param("userId") Long userId,
                               @Param("workerId") String workerId,
                               @Param("pending") FuzzTaskPo.TaskStatus pending);

    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE FuzzTaskPo t SET t.status = :running, t.startedAt = :startedAt, "
         + "t.progress = 0, t.checkLogsJson = :checkLogsJson, "
         + "t.leaseExpiresAt = :leaseExpiresAt "
         + "WHERE t.id = :taskId AND t.status = :pending AND t.workerId = :workerId")
    int startTaskIfStillPending(@Param("taskId") Long taskId,
                                @Param("running") FuzzTaskPo.TaskStatus running,
                                @Param("startedAt") LocalDateTime startedAt,
                                @Param("workerId") String workerId,
                                @Param("leaseExpiresAt") LocalDateTime leaseExpiresAt,
                                @Param("checkLogsJson") String checkLogsJson,
                                @Param("pending") FuzzTaskPo.TaskStatus pending);

    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE FuzzTaskPo t SET t.leaseExpiresAt = :leaseExpiresAt "
         + "WHERE t.id = :taskId AND t.workerId = :workerId "
         + "AND t.status IN (:activeStatuses)")
    int renewOwnedActiveLease(@Param("taskId") Long taskId,
                              @Param("workerId") String workerId,
                              @Param("leaseExpiresAt") LocalDateTime leaseExpiresAt,
                              @Param("activeStatuses") List<FuzzTaskPo.TaskStatus> activeStatuses);

    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE FuzzTaskPo t SET t.workerId = NULL, t.leaseExpiresAt = :expiredAt "
         + "WHERE t.id = :taskId AND t.workerId = :workerId "
         + "AND t.status IN (:activeStatuses)")
    int releaseOwnedActiveLease(@Param("taskId") Long taskId,
                                @Param("workerId") String workerId,
                                @Param("expiredAt") LocalDateTime expiredAt,
                                @Param("activeStatuses") List<FuzzTaskPo.TaskStatus> activeStatuses);

    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE FuzzTaskPo t SET t.status = :failed, t.completedAt = :completedAt, "
         + "t.progress = 100, t.errorMessage = :errorMessage, t.checkLogsJson = :checkLogsJson, "
         + "t.workerId = NULL, t.leaseExpiresAt = NULL "
         + "WHERE t.status IN (:activeStatuses) "
         + "AND (t.leaseExpiresAt IS NULL OR t.leaseExpiresAt < :expiredBefore)")
    int failExpiredActiveTasks(@Param("failed") FuzzTaskPo.TaskStatus failed,
                               @Param("completedAt") LocalDateTime completedAt,
                               @Param("errorMessage") String errorMessage,
                               @Param("checkLogsJson") String checkLogsJson,
                               @Param("activeStatuses") List<FuzzTaskPo.TaskStatus> activeStatuses,
                               @Param("expiredBefore") LocalDateTime expiredBefore);

    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE FuzzTaskPo t SET t.status = :completed, t.completedAt = :completedAt, "
         + "t.processingTimeMs = :processingTimeMs, t.progress = 100, t.outcome = :outcome, "
         + "t.effectiveSeed = :effectiveSeed, t.iterations = :iterations, "
         + "t.generatedPaths = :generatedPaths, t.elapsedMs = :elapsedMs, "
         + "t.eligibilityJson = :eligibilityJson, t.limitationsJson = :limitationsJson, "
         + "t.findingCount = :findingCount, t.errorMessage = NULL, "
         + "t.workerId = NULL, t.leaseExpiresAt = NULL, "
         + "t.checkLogsJson = :checkLogsJson "
         + "WHERE t.id = :taskId AND t.status = :running")
    int completeTaskIfRunning(@Param("taskId") Long taskId,
                              @Param("completed") FuzzTaskPo.TaskStatus completed,
                              @Param("completedAt") LocalDateTime completedAt,
                              @Param("processingTimeMs") Long processingTimeMs,
                              @Param("outcome") FuzzOutcome outcome,
                              @Param("effectiveSeed") Long effectiveSeed,
                              @Param("iterations") Integer iterations,
                              @Param("generatedPaths") Long generatedPaths,
                              @Param("elapsedMs") Long elapsedMs,
                              @Param("eligibilityJson") String eligibilityJson,
                              @Param("limitationsJson") String limitationsJson,
                              @Param("findingCount") Integer findingCount,
                              @Param("checkLogsJson") String checkLogsJson,
                              @Param("running") FuzzTaskPo.TaskStatus running);

    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE FuzzTaskPo t SET t.status = :failed, t.completedAt = :completedAt, "
         + "t.processingTimeMs = :processingTimeMs, t.progress = 100, "
         + "t.errorMessage = :errorMessage, t.checkLogsJson = :checkLogsJson, "
         + "t.workerId = NULL, t.leaseExpiresAt = NULL "
         + "WHERE t.id = :taskId AND t.status IN (:activeStatuses)")
    int failTaskIfActive(@Param("taskId") Long taskId,
                         @Param("failed") FuzzTaskPo.TaskStatus failed,
                         @Param("completedAt") LocalDateTime completedAt,
                         @Param("processingTimeMs") Long processingTimeMs,
                         @Param("errorMessage") String errorMessage,
                         @Param("checkLogsJson") String checkLogsJson,
                         @Param("activeStatuses") List<FuzzTaskPo.TaskStatus> activeStatuses);

    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE FuzzTaskPo t SET t.status = :cancelled, t.completedAt = :completedAt, "
         + "t.progress = 100, t.workerId = NULL, t.leaseExpiresAt = NULL "
         + "WHERE t.id = :taskId AND t.status IN (:activeStatuses)")
    int cancelTaskIfStillActive(@Param("taskId") Long taskId,
                                @Param("cancelled") FuzzTaskPo.TaskStatus cancelled,
                                @Param("completedAt") LocalDateTime completedAt,
                                @Param("activeStatuses") List<FuzzTaskPo.TaskStatus> activeStatuses);

    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE FuzzTaskPo t SET t.progress = :progress, t.progressStage = :stage "
         + "WHERE t.id = :taskId AND t.status IN ('PENDING', 'RUNNING')")
    int updateProgressIfActive(@Param("taskId") Long taskId, @Param("progress") int progress,
                               @Param("stage") TaskProgressStage stage);
}
