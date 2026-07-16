package cn.edu.nju.Iot_Verify.repository.projection;

import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzExplorationMode;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzOutcome;
import cn.edu.nju.Iot_Verify.po.FuzzTaskPo;

import java.time.LocalDateTime;

/**
 * Closed projection for task/run lists. Deliberately omits the frozen
 * {@code modelInputSnapshotJson} and diagnostic-log LONGTEXT columns; detail
 * endpoints load the full entity when complete snapshot validation is required.
 */
public interface FuzzTaskSummaryProjection {

    Long getId();

    Long getUserId();

    FuzzTaskPo.TaskStatus getStatus();

    LocalDateTime getCreatedAt();

    LocalDateTime getStartedAt();

    LocalDateTime getCompletedAt();

    Long getProcessingTimeMs();

    String getErrorMessage();

    Integer getProgress();

    String getTargetSpecIdsJson();

    Integer getMaxIterations();

    Integer getPathLength();

    Integer getPopulationSize();

    Long getSeed();

    FuzzExplorationMode getExplorationMode();

    String getModelSnapshotJson();

    FuzzOutcome getOutcome();

    Long getEffectiveSeed();

    Integer getIterations();

    Long getGeneratedPaths();

    Long getElapsedMs();

    String getEligibilityJson();

    String getLimitationsJson();

    Integer getFindingCount();
}
