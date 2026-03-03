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
}
