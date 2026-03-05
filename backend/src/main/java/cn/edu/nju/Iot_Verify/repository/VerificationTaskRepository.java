package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;
import org.springframework.stereotype.Repository;
import org.springframework.transaction.annotation.Transactional;

import java.time.LocalDateTime;
import java.util.List;
import java.util.Optional;

/**
 * 验证任务仓储接口
 */
@Repository
public interface VerificationTaskRepository extends JpaRepository<VerificationTaskPo, Long> {

    /**
     * 根据用户ID查询所有任务（按创建时间降序）
     */
    List<VerificationTaskPo> findByUserIdOrderByCreatedAtDesc(Long userId);

    /**
     * 根据ID和用户ID查询任务
     */
    Optional<VerificationTaskPo> findByIdAndUserId(Long id, Long userId);

    /**
     * 根据用户ID和状态查询任务
     */
    List<VerificationTaskPo> findByUserIdAndStatus(Long userId, VerificationTaskPo.TaskStatus status);

    /**
     * 根据状态列表查询任务（用于启动时清理僵尸任务）
     */
    List<VerificationTaskPo> findByStatusIn(List<VerificationTaskPo.TaskStatus> statuses);

    /**
     * 删除用户的所有任务
     */
    void deleteByUserId(Long userId);

    /**
     * Atomically complete a task only if it has not been cancelled.
     * Returns 1 if updated, 0 if the task was already CANCELLED.
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE VerificationTaskPo t SET t.status = :newStatus, t.completedAt = :completedAt, "
         + "t.progress = 100, t.isSafe = :isSafe, t.violatedSpecCount = :violatedSpecCount, "
         + "t.checkLogsJson = :checkLogsJson, t.nusmvOutput = :nusmvOutput, "
         + "t.errorMessage = :errorMessage, t.processingTimeMs = :processingTimeMs "
         + "WHERE t.id = :taskId AND t.status <> :cancelledStatus")
    int completeTaskIfNotCancelled(@Param("taskId") Long taskId,
                                   @Param("newStatus") VerificationTaskPo.TaskStatus newStatus,
                                   @Param("completedAt") LocalDateTime completedAt,
                                   @Param("isSafe") Boolean isSafe,
                                   @Param("violatedSpecCount") Integer violatedSpecCount,
                                   @Param("checkLogsJson") String checkLogsJson,
                                   @Param("nusmvOutput") String nusmvOutput,
                                   @Param("errorMessage") String errorMessage,
                                   @Param("processingTimeMs") Long processingTimeMs,
                                   @Param("cancelledStatus") VerificationTaskPo.TaskStatus cancelledStatus);

    /**
     * Atomically fail a task only if it has not been cancelled.
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE VerificationTaskPo t SET t.status = :newStatus, t.completedAt = :completedAt, "
         + "t.progress = 100, t.isSafe = false, t.errorMessage = :errorMessage, "
         + "t.checkLogsJson = :checkLogsJson, t.processingTimeMs = :processingTimeMs "
         + "WHERE t.id = :taskId AND t.status <> :cancelledStatus")
    int failTaskIfNotCancelled(@Param("taskId") Long taskId,
                               @Param("newStatus") VerificationTaskPo.TaskStatus newStatus,
                               @Param("completedAt") LocalDateTime completedAt,
                               @Param("errorMessage") String errorMessage,
                               @Param("checkLogsJson") String checkLogsJson,
                               @Param("processingTimeMs") Long processingTimeMs,
                               @Param("cancelledStatus") VerificationTaskPo.TaskStatus cancelledStatus);

    /**
     * Atomically transition a task from PENDING to RUNNING.
     * Closes the race window where a concurrent cancel could be overwritten by a plain save().
     * Returns 1 if updated, 0 if the task is no longer PENDING (e.g. already CANCELLED).
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE VerificationTaskPo t SET t.status = :running, "
         + "t.startedAt = :startedAt, t.progress = :progress, "
         + "t.checkLogsJson = :checkLogsJson "
         + "WHERE t.id = :taskId AND t.status = :pendingStatus")
    int startTaskIfStillPending(@Param("taskId") Long taskId,
                                @Param("running") VerificationTaskPo.TaskStatus running,
                                @Param("startedAt") LocalDateTime startedAt,
                                @Param("progress") int progress,
                                @Param("checkLogsJson") String checkLogsJson,
                                @Param("pendingStatus") VerificationTaskPo.TaskStatus pendingStatus);

    /**
     * Atomically cancel a task only if it is still PENDING or RUNNING.
     * Prevents overwriting a legitimately COMPLETED or FAILED status.
     * Returns 1 if updated, 0 if the task already finished.
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE VerificationTaskPo t SET t.status = :cancelledStatus, "
         + "t.completedAt = :completedAt, t.progress = 100 "
         + "WHERE t.id = :taskId AND t.status IN (:activeStatuses)")
    int cancelTaskIfStillActive(@Param("taskId") Long taskId,
                                @Param("cancelledStatus") VerificationTaskPo.TaskStatus cancelledStatus,
                                @Param("completedAt") LocalDateTime completedAt,
                                @Param("activeStatuses") List<VerificationTaskPo.TaskStatus> activeStatuses);

    /**
     * Atomically update progress only if the task is still active (PENDING or RUNNING).
     * Prevents overwriting progress on terminal-state tasks.
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE VerificationTaskPo t SET t.progress = :progress "
         + "WHERE t.id = :taskId AND t.status IN ('PENDING', 'RUNNING')")
    int updateProgressIfActive(@Param("taskId") Long taskId, @Param("progress") int progress);
}
