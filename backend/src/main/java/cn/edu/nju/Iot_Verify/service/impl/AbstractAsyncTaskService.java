package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.model.TaskCancellationOutcome;
import cn.edu.nju.Iot_Verify.dto.model.TaskCancellationResultDto;
import cn.edu.nju.Iot_Verify.dto.model.TaskProgressStage;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.po.TaskView;
import cn.edu.nju.Iot_Verify.service.AsyncTaskExecutionControl;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.extern.slf4j.Slf4j;

import java.time.LocalDateTime;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

/**
 * 异步任务管理基类。
 *
 * <p>提取 VerificationServiceImpl 与 SimulationServiceImpl 中完全相同的：
 * <ul>
 *   <li>3 个并发容器（runningTasks / taskProgress / cancelledTasks）+ 语义操作方法</li>
 *   <li>serializeCheckLogs / readCheckLogs / writeCheckLogs / truncateOutput</li>
 *   <li>updateTaskProgress / getTaskProgress / cancelTask / handleCancellation</li>
 * </ul>
 *
 * <p>子类通过实现 Repository 委托钩子来适配具体实体类型。
 *
 * @param <T> 任务 PO 类型，必须实现 {@link TaskView}
 */
@Slf4j
public abstract class AbstractAsyncTaskService<T extends TaskView>
        implements AsyncTaskExecutionControl {

    protected static final int MAX_OUTPUT_LENGTH = 10_000;
    private static final String DIAGNOSTIC_LOSS_MESSAGE =
            "[diagnostic-loss] Task diagnostic logs could not be serialized or parsed.";
    private static final String DIAGNOSTIC_LOSS_JSON =
            "[\"[diagnostic-loss] Task diagnostic logs could not be serialized or parsed.\"]";
    protected final ObjectMapper objectMapper;

    // ── 并发容器（private，通过语义操作方法暴露）──────────────────────

    private final ConcurrentHashMap<Long, Thread> runningTasks = new ConcurrentHashMap<>();
    private final ConcurrentHashMap<Long, TaskProgressState> taskProgress = new ConcurrentHashMap<>();
    private final Set<Long> cancelledTasks = ConcurrentHashMap.newKeySet();

    protected AbstractAsyncTaskService(ObjectMapper objectMapper,
                                       String taskResourceType) {
        this.objectMapper = objectMapper;
        this.taskResourceType = taskResourceType;
    }

    /** 用于 ResourceNotFoundException 和日志输出的资源类型名称 */
    private final String taskResourceType;

    // ── 容器语义操作方法（protected，子类异步编排使用）──────────────────

    protected void registerRunningTask(Long taskId, Thread thread) {
        runningTasks.put(taskId, thread);
    }

    protected boolean isTaskCancelled(Long taskId) {
        return cancelledTasks.contains(taskId);
    }

    /**
     * 从取消标记集合中移除任务。
     * @return true 如果任务确实在已取消集合中（即需要执行取消收尾）
     */
    protected boolean removeCancelledMark(Long taskId) {
        return cancelledTasks.remove(taskId);
    }

    protected void removeRunningTask(Long taskId) {
        runningTasks.remove(taskId);
    }

    protected void removeTaskProgress(Long taskId) {
        taskProgress.remove(taskId);
    }

    protected enum LocalExecutionStopResult {
        NONE(false, false),
        STOPPED_BEFORE_START(true, false),
        STOP_REQUESTED(true, true);

        private final boolean requested;
        private final boolean mayStillBeStopping;

        LocalExecutionStopResult(boolean requested, boolean mayStillBeStopping) {
            this.requested = requested;
            this.mayStillBeStopping = mayStillBeStopping;
        }
    }

    @Override
    public boolean requestLocalExecutionStop(Long taskId) {
        if (taskId == null) return false;
        return stopLocalExecution(taskId).requested;
    }

    private LocalExecutionStopResult stopLocalExecution(Long taskId) {
        LocalExecutionStopResult additionalStop = Objects.requireNonNull(
                stopAdditionalLocalExecution(taskId),
                "stopAdditionalLocalExecution must not return null");
        Thread taskThread = runningTasks.get(taskId);
        if (taskThread != null && taskThread.isAlive()) {
            taskThread.interrupt();
            return LocalExecutionStopResult.STOP_REQUESTED;
        }
        return additionalStop;
    }

    /** Lets a domain service stop work that is accepted locally but has no runner thread yet. */
    protected LocalExecutionStopResult stopAdditionalLocalExecution(Long taskId) {
        return LocalExecutionStopResult.NONE;
    }

    // ── 直接搬入的具体方法（无领域差异）─────────────────────────────

    protected String serializeCheckLogs(List<String> logs) {
        try {
            return objectMapper.writeValueAsString(logs == null ? List.of() : logs);
        } catch (Exception e) {
            log.warn("Failed to serialize check logs", e);
            return DIAGNOSTIC_LOSS_JSON;
        }
    }

    protected List<String> readCheckLogs(T task) {
        if (task == null || task.getCheckLogsJson() == null || task.getCheckLogsJson().isBlank()) {
            return new ArrayList<>();
        }
        try {
            return objectMapper.readValue(task.getCheckLogsJson(), new TypeReference<List<String>>() {});
        } catch (Exception e) {
            log.warn("Failed to parse checkLogsJson for {} {}", taskResourceType, task.getId(), e);
            return new ArrayList<>(List.of(DIAGNOSTIC_LOSS_MESSAGE));
        }
    }

    protected void writeCheckLogs(T task, List<String> logs) {
        if (task == null) return;
        try {
            task.setCheckLogsJson(objectMapper.writeValueAsString(logs == null ? List.of() : logs));
        } catch (Exception e) {
            log.warn("Failed to serialize check logs for {} {}", taskResourceType, task.getId(), e);
            task.setCheckLogsJson(DIAGNOSTIC_LOSS_JSON);
        }
    }

    protected String truncateOutput(String output) {
        if (output == null) return null;
        return output.length() > MAX_OUTPUT_LENGTH
                ? output.substring(0, MAX_OUTPUT_LENGTH) + "\n... (output truncated)" : output;
    }

    // ── 可提取且保留状态机差异钩子的方法 ──────────────────────────────

    /**
     * 更新任务进度。
     * 逻辑来源：VerificationServiceImpl:L532-539, SimulationServiceImpl:L528-535
     */
    protected void updateTaskProgress(Long taskId, int progress, TaskProgressStage stage) {
        Long requiredTaskId = Objects.requireNonNull(taskId, "taskId must not be null");
        TaskProgressStage requiredStage = Objects.requireNonNull(stage, "stage must not be null");
        int clamped = Math.min(100, Math.max(0, progress));
        TaskProgressState next = new TaskProgressState(clamped, requiredStage);
        TaskProgressState previous = taskProgress.put(requiredTaskId, next);
        if (!Objects.equals(previous, next)) {
            atomicUpdateProgress(requiredTaskId, clamped, requiredStage);
        }
        log.debug("{} {} progress: {}% - {}", taskResourceType, requiredTaskId, progress, requiredStage);
    }

    /**
     * 获取任务进度。
     *
     * <p><b>语义保真</b>：不存在或越权的任务抛 {@link ResourceNotFoundException}，
     * 不得返回 0 或静默忽略。
     *
     * <p>逻辑来源：VerificationServiceImpl:L543-563, SimulationServiceImpl:L274-294
     */
    protected int getTaskProgress(Long userId, Long taskId) {
        // 归属校验——不存在则抛异常
        T task = findTaskByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException(taskResourceType, taskId));

        // 优先使用内存值（当前实例上的活跃任务）
        TaskProgressState progress = taskProgress.get(taskId);
        if (progress != null) {
            return progress.progress();
        }
        // 退回 DB 列（任务在其他实例上或重启后）
        if (task.getProgress() != null) {
            return task.getProgress();
        }
        // 终态推断
        if (task.isTerminalStatus()) {
            return 100;
        }
        return 0;
    }

    /**
     * 取消任务。
     *
     * <p><b>语义保真</b>：先归属校验 → 原子 DB cancel → 返回实际取消结果和终态。
     *
     * <p>逻辑来源：VerificationServiceImpl:L504-529, SimulationServiceImpl:L298-321
     */
    protected TaskCancellationResultDto cancelTask(Long userId, Long taskId) {
        T task = findTaskByIdAndUserId(taskId, userId)
                .orElseThrow(() -> new ResourceNotFoundException(taskResourceType, taskId));
        boolean markerWasPresent = cancelledTasks.contains(taskId);
        cancelledTasks.add(taskId);
        try {
            int updated = atomicCancelTask(taskId, LocalDateTime.now());
            if (updated == 0) {
                T currentTask = findTaskByIdAndUserId(taskId, userId)
                        .orElseThrow(() -> new ResourceNotFoundException(taskResourceType, taskId));
                String currentStatus = currentTask.getTaskStatusName();
                boolean alreadyCancelled = currentTask.isCancelledStatus();
                LocalExecutionStopResult localStop = alreadyCancelled
                        ? stopLocalExecution(taskId)
                        : LocalExecutionStopResult.NONE;
                if (!markerWasPresent
                        && localStop != LocalExecutionStopResult.STOP_REQUESTED) {
                    cancelledTasks.remove(taskId);
                }
                return TaskCancellationResultDto.builder()
                        .taskId(taskId)
                        .cancellationAccepted(false)
                        .cancellationOutcome(cancellationOutcomeFor(currentStatus))
                        .taskStatus(currentStatus)
                        .executionMayStillBeStopping(localStop.mayStillBeStopping)
                        .build();
            }

            LocalExecutionStopResult localStop = stopLocalExecution(taskId);
            boolean runningExecutionMayStillBeStopping =
                    localStop != LocalExecutionStopResult.STOPPED_BEFORE_START;
            if (!markerWasPresent
                    && localStop != LocalExecutionStopResult.STOP_REQUESTED) {
                cancelledTasks.remove(taskId);
            }
            return TaskCancellationResultDto.builder()
                    .taskId(taskId)
                    .cancellationAccepted(true)
                    .cancellationOutcome(TaskCancellationOutcome.ACCEPTED)
                    .taskStatus("CANCELLED")
                    .executionMayStillBeStopping(runningExecutionMayStillBeStopping)
                    .build();
        } catch (RuntimeException e) {
            if (!markerWasPresent) {
                cancelledTasks.remove(taskId);
            }
            throw e;
        }
    }

    private static TaskCancellationOutcome cancellationOutcomeFor(String status) {
        return switch (status) {
            case "CANCELLED" -> TaskCancellationOutcome.ALREADY_CANCELLED;
            case "COMPLETED" -> TaskCancellationOutcome.ALREADY_COMPLETED;
            case "FAILED" -> TaskCancellationOutcome.ALREADY_FAILED;
            default -> TaskCancellationOutcome.NO_LONGER_CANCELLABLE;
        };
    }

    /**
     * 处理取消收尾。子类可 override 添加额外清理逻辑（如日志）。
     *
     * <p>逻辑来源：VerificationServiceImpl:L758-769, SimulationServiceImpl:L515-526
     */
    protected void handleCancellation(T task) {
        log.info("Handling cancellation for {}: {}", taskResourceType, task.getId());
        int updated = atomicCancelTask(task.getId(), LocalDateTime.now());
        if (updated == 0) {
            log.info("{} {} already finished (COMPLETED/FAILED), skipping cancel", taskResourceType, task.getId());
        }
    }

    // ── 子类实现的 Repository 委托钩子 ───────────────────────────────

    /**
     * 根据 ID 和用户 ID 查找任务。
     */
    protected abstract Optional<T> findTaskByIdAndUserId(Long id, Long userId);

    /**
     * 原子取消任务（仅当任务处于 PENDING 或 RUNNING 状态时）。
     * @return 影响行数（0 表示任务已不在可取消状态）
     */
    protected abstract int atomicCancelTask(Long taskId, LocalDateTime completedAt);

    /**
     * 原子更新任务进度（仅当任务仍在活跃状态时）。
     */
    protected abstract int atomicUpdateProgress(Long taskId, int progress, TaskProgressStage stage);

    private record TaskProgressState(int progress, TaskProgressStage stage) {
    }
}
