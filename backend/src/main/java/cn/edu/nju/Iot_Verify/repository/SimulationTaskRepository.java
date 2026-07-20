package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
import cn.edu.nju.Iot_Verify.dto.model.TaskProgressStage;
import jakarta.persistence.LockModeType;
import org.springframework.data.jpa.repository.JpaRepository;
import org.springframework.data.jpa.repository.Lock;
import org.springframework.data.jpa.repository.Modifying;
import org.springframework.data.jpa.repository.Query;
import org.springframework.data.repository.query.Param;
import org.springframework.stereotype.Repository;
import org.springframework.transaction.annotation.Transactional;

import java.time.LocalDateTime;
import java.util.List;
import java.util.Optional;

@Repository
public interface SimulationTaskRepository extends JpaRepository<SimulationTaskPo, Long>, DatabaseClockRepository {

    @Lock(LockModeType.PESSIMISTIC_WRITE)
    @Query("SELECT t FROM SimulationTaskPo t WHERE t.id = :taskId")
    Optional<SimulationTaskPo> findByIdForUpdate(@Param("taskId") Long taskId);

    long countByUserId(Long userId);

    long countByUserIdAndStatusIn(Long userId, List<SimulationTaskPo.TaskStatus> statuses);

    Optional<SimulationTaskPo> findByIdAndUserId(Long id, Long userId);

    List<SimulationTaskPo> findByUserIdOrderByCreatedAtDesc(Long userId);

    List<SimulationTaskPo> findByUserIdAndIdNotInOrderByCreatedAtDesc(Long userId, List<Long> excludedIds);

    List<SimulationTaskPo> findByUserIdAndStatusNotOrderByCreatedAtDesc(
            Long userId, SimulationTaskPo.TaskStatus status);

    List<SimulationTaskPo> findByUserIdAndStatusNotAndIdNotInOrderByCreatedAtDesc(
            Long userId, SimulationTaskPo.TaskStatus status, List<Long> excludedIds);

    void deleteByUserIdAndSimulationTraceId(Long userId, Long simulationTraceId);

    void deleteByUserId(Long userId);

    List<SimulationTaskPo> findByUserIdAndStatus(Long userId, SimulationTaskPo.TaskStatus status);

    /**
     * Atomically complete a simulation task only while it is RUNNING.
     * Terminal states are immutable: CANCELLED/COMPLETED/FAILED must not be overwritten.
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.status = :newStatus, t.completedAt = :completedAt, "
         + "t.progress = 100, t.steps = :steps, t.simulationTraceId = :simulationTraceId, "
         + "t.errorMessage = :errorMessage, t.checkLogsJson = :checkLogsJson, "
         + "t.generationIssuesJson = :generationIssuesJson, t.processingTimeMs = :processingTimeMs, "
         + "t.workerId = NULL, t.leaseExpiresAt = NULL "
         + "WHERE t.id = :taskId AND t.status = :runningStatus "
         + "AND t.workerId = :workerId AND t.leaseExpiresAt > :currentTime")
    int completeTaskIfRunning(@Param("taskId") Long taskId,
                              @Param("newStatus") SimulationTaskPo.TaskStatus newStatus,
                              @Param("completedAt") LocalDateTime completedAt,
                              @Param("steps") Integer steps,
                              @Param("simulationTraceId") Long simulationTraceId,
                              @Param("errorMessage") String errorMessage,
                              @Param("checkLogsJson") String checkLogsJson,
                              @Param("generationIssuesJson") String generationIssuesJson,
                              @Param("processingTimeMs") Long processingTimeMs,
                              @Param("runningStatus") SimulationTaskPo.TaskStatus runningStatus,
                              @Param("workerId") String workerId,
                              @Param("currentTime") LocalDateTime currentTime);

    /**
     * Atomically fail a simulation task only while it is still active.
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.status = :newStatus, t.completedAt = :completedAt, "
         + "t.progress = 100, t.errorMessage = :errorMessage, "
         + "t.checkLogsJson = :checkLogsJson, t.processingTimeMs = :processingTimeMs, "
         + "t.workerId = NULL, t.leaseExpiresAt = NULL "
         + "WHERE t.id = :taskId AND t.status IN (:activeStatuses) "
         + "AND t.workerId = :workerId AND t.leaseExpiresAt > :currentTime")
    int failTaskIfActive(@Param("taskId") Long taskId,
                         @Param("newStatus") SimulationTaskPo.TaskStatus newStatus,
                         @Param("completedAt") LocalDateTime completedAt,
                         @Param("errorMessage") String errorMessage,
                         @Param("checkLogsJson") String checkLogsJson,
                         @Param("processingTimeMs") Long processingTimeMs,
                         @Param("activeStatuses") List<SimulationTaskPo.TaskStatus> activeStatuses,
                         @Param("workerId") String workerId,
                         @Param("currentTime") LocalDateTime currentTime);

    /**
     * Atomically transition a task from PENDING to RUNNING.
     * Closes the race window where a concurrent cancel could be overwritten by a plain save().
     * Returns 1 if updated, 0 if the task is no longer PENDING (e.g. already CANCELLED).
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.status = :running, "
         + "t.startedAt = :startedAt, t.progress = :progress, "
         + "t.checkLogsJson = :checkLogsJson, t.leaseExpiresAt = :leaseExpiresAt "
         + "WHERE t.id = :taskId AND t.status = :pendingStatus "
         + "AND t.workerId = :workerId AND t.leaseExpiresAt > :currentTime")
    int startTaskIfStillPending(@Param("taskId") Long taskId,
                                @Param("running") SimulationTaskPo.TaskStatus running,
                                @Param("startedAt") LocalDateTime startedAt,
                                @Param("progress") int progress,
                                @Param("checkLogsJson") String checkLogsJson,
                                @Param("pendingStatus") SimulationTaskPo.TaskStatus pendingStatus,
                                @Param("workerId") String workerId,
                                @Param("currentTime") LocalDateTime currentTime,
                                @Param("leaseExpiresAt") LocalDateTime leaseExpiresAt);

    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.leaseExpiresAt = :leaseExpiresAt "
         + "WHERE t.id = :taskId AND t.workerId = :workerId "
         + "AND t.status IN (:activeStatuses) AND t.leaseExpiresAt > :currentTime")
    int renewOwnedActiveLease(@Param("taskId") Long taskId,
                              @Param("workerId") String workerId,
                              @Param("currentTime") LocalDateTime currentTime,
                              @Param("leaseExpiresAt") LocalDateTime leaseExpiresAt,
                              @Param("activeStatuses") List<SimulationTaskPo.TaskStatus> activeStatuses);

    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.workerId = NULL, t.leaseExpiresAt = :expiredAt "
         + "WHERE t.id = :taskId AND t.workerId = :workerId "
         + "AND t.status IN (:activeStatuses)")
    int releaseOwnedActiveLease(@Param("taskId") Long taskId,
                                @Param("workerId") String workerId,
                                @Param("expiredAt") LocalDateTime expiredAt,
                                @Param("activeStatuses") List<SimulationTaskPo.TaskStatus> activeStatuses);

    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.status = :failed, t.completedAt = :completedAt, "
         + "t.progress = 100, t.errorMessage = :errorMessage, t.checkLogsJson = :checkLogsJson, "
         + "t.workerId = NULL, t.leaseExpiresAt = NULL "
         + "WHERE t.status IN (:activeStatuses) "
         + "AND (t.leaseExpiresAt IS NULL OR t.leaseExpiresAt <= :expiredBefore)")
    int failExpiredActiveTasks(@Param("failed") SimulationTaskPo.TaskStatus failed,
                               @Param("completedAt") LocalDateTime completedAt,
                               @Param("errorMessage") String errorMessage,
                               @Param("checkLogsJson") String checkLogsJson,
                               @Param("activeStatuses") List<SimulationTaskPo.TaskStatus> activeStatuses,
                               @Param("expiredBefore") LocalDateTime expiredBefore);

    /**
     * Atomically cancel a task only if it is still PENDING or RUNNING.
     * Prevents overwriting a legitimately COMPLETED or FAILED status.
     * Returns 1 if updated, 0 if the task already finished.
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.status = :cancelledStatus, "
         + "t.completedAt = :completedAt, t.progress = 100, "
         + "t.workerId = NULL, t.leaseExpiresAt = NULL "
         + "WHERE t.id = :taskId AND t.status IN (:activeStatuses)")
    int cancelTaskIfStillActive(@Param("taskId") Long taskId,
                                @Param("cancelledStatus") SimulationTaskPo.TaskStatus cancelledStatus,
                                @Param("completedAt") LocalDateTime completedAt,
                                @Param("activeStatuses") List<SimulationTaskPo.TaskStatus> activeStatuses);

    /**
     * Atomically update progress only if the task is still active (PENDING or RUNNING).
     * Prevents overwriting progress on terminal-state tasks.
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.progress = :progress, t.progressStage = :stage "
         + "WHERE t.id = :taskId AND t.status IN ('PENDING', 'RUNNING') "
         + "AND t.workerId = :workerId AND t.leaseExpiresAt > :currentTime")
    int updateProgressIfActive(@Param("taskId") Long taskId, @Param("progress") int progress,
                               @Param("stage") TaskProgressStage stage,
                               @Param("workerId") String workerId,
                               @Param("currentTime") LocalDateTime currentTime);

    /** Persist the assumptions under which this task will run without replacing task state. */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.isAttack = :isAttack, "
         + "t.attackBudget = :attackBudget, t.enablePrivacy = :enablePrivacy, "
         + "t.modeledDeviceAttackPointCount = :devicePointCount, "
         + "t.modeledFalsifiableReadingDeviceCount = :falsifiableReadingDeviceCount, "
         + "t.modeledAutomationLinkAttackPointCount = :linkPointCount, "
         + "t.modelSnapshotJson = :modelSnapshotJson, "
         + "t.modelSemanticsJson = :modelSemanticsJson "
         + "WHERE t.id = :taskId")
    int updateModelContext(@Param("taskId") Long taskId,
                           @Param("isAttack") boolean isAttack,
                           @Param("attackBudget") int attackBudget,
                           @Param("enablePrivacy") boolean enablePrivacy,
                           @Param("devicePointCount") int devicePointCount,
                           @Param("falsifiableReadingDeviceCount") int falsifiableReadingDeviceCount,
                           @Param("linkPointCount") int linkPointCount,
                           @Param("modelSnapshotJson") String modelSnapshotJson,
                           @Param("modelSemanticsJson") String modelSemanticsJson);
}
