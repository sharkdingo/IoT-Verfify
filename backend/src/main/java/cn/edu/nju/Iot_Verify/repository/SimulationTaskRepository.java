package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
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
public interface SimulationTaskRepository extends JpaRepository<SimulationTaskPo, Long> {

    Optional<SimulationTaskPo> findByIdAndUserId(Long id, Long userId);

    List<SimulationTaskPo> findByStatusIn(List<SimulationTaskPo.TaskStatus> statuses);

    List<SimulationTaskPo> findByUserIdOrderByCreatedAtDesc(Long userId);

    void deleteByUserId(Long userId);

    List<SimulationTaskPo> findByUserIdAndStatus(Long userId, SimulationTaskPo.TaskStatus status);

    /**
     * Atomically complete a simulation task only if it has not been cancelled.
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.status = :newStatus, t.completedAt = :completedAt, "
         + "t.progress = 100, t.steps = :steps, t.simulationTraceId = :simulationTraceId, "
         + "t.errorMessage = :errorMessage, t.checkLogsJson = :checkLogsJson, "
         + "t.processingTimeMs = :processingTimeMs "
         + "WHERE t.id = :taskId AND t.status <> :cancelledStatus")
    int completeTaskIfNotCancelled(@Param("taskId") Long taskId,
                                   @Param("newStatus") SimulationTaskPo.TaskStatus newStatus,
                                   @Param("completedAt") LocalDateTime completedAt,
                                   @Param("steps") Integer steps,
                                   @Param("simulationTraceId") Long simulationTraceId,
                                   @Param("errorMessage") String errorMessage,
                                   @Param("checkLogsJson") String checkLogsJson,
                                   @Param("processingTimeMs") Long processingTimeMs,
                                   @Param("cancelledStatus") SimulationTaskPo.TaskStatus cancelledStatus);

    /**
     * Atomically fail a simulation task only if it has not been cancelled.
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.status = :newStatus, t.completedAt = :completedAt, "
         + "t.progress = 100, t.errorMessage = :errorMessage, "
         + "t.checkLogsJson = :checkLogsJson, t.processingTimeMs = :processingTimeMs "
         + "WHERE t.id = :taskId AND t.status <> :cancelledStatus")
    int failTaskIfNotCancelled(@Param("taskId") Long taskId,
                               @Param("newStatus") SimulationTaskPo.TaskStatus newStatus,
                               @Param("completedAt") LocalDateTime completedAt,
                               @Param("errorMessage") String errorMessage,
                               @Param("checkLogsJson") String checkLogsJson,
                               @Param("processingTimeMs") Long processingTimeMs,
                               @Param("cancelledStatus") SimulationTaskPo.TaskStatus cancelledStatus);

    /**
     * Atomically transition a task from PENDING to RUNNING.
     * Closes the race window where a concurrent cancel could be overwritten by a plain save().
     * Returns 1 if updated, 0 if the task is no longer PENDING (e.g. already CANCELLED).
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.status = :running, "
         + "t.startedAt = :startedAt, t.progress = :progress, "
         + "t.checkLogsJson = :checkLogsJson "
         + "WHERE t.id = :taskId AND t.status = :pendingStatus")
    int startTaskIfStillPending(@Param("taskId") Long taskId,
                                @Param("running") SimulationTaskPo.TaskStatus running,
                                @Param("startedAt") LocalDateTime startedAt,
                                @Param("progress") int progress,
                                @Param("checkLogsJson") String checkLogsJson,
                                @Param("pendingStatus") SimulationTaskPo.TaskStatus pendingStatus);

    /**
     * Atomically cancel a task only if it is still PENDING or RUNNING.
     * Prevents overwriting a legitimately COMPLETED or FAILED status.
     * Returns 1 if updated, 0 if the task already finished.
     */
    @Transactional
    @Modifying(clearAutomatically = true)
    @Query("UPDATE SimulationTaskPo t SET t.status = :cancelledStatus, "
         + "t.completedAt = :completedAt, t.progress = 100 "
         + "WHERE t.id = :taskId AND t.status IN (:activeStatuses)")
    int cancelTaskIfStillActive(@Param("taskId") Long taskId,
                                @Param("cancelledStatus") SimulationTaskPo.TaskStatus cancelledStatus,
                                @Param("completedAt") LocalDateTime completedAt,
                                @Param("activeStatuses") List<SimulationTaskPo.TaskStatus> activeStatuses);
}
