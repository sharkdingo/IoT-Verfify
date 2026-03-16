package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.po.TaskView;
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
public abstract class AbstractAsyncTaskService<T extends TaskView> {

    protected static final int MAX_OUTPUT_LENGTH = 10_000;
    protected final ObjectMapper objectMapper;

    // ── 并发容器（private，通过语义操作方法暴露）──────────────────────

    private final ConcurrentHashMap<Long, Thread> runningTasks = new ConcurrentHashMap<>();
    private final ConcurrentHashMap<Long, Integer> taskProgress = new ConcurrentHashMap<>();
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

    protected void markCancelled(Long taskId) {
        cancelledTasks.add(taskId);
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

    protected Thread getRunningTaskThread(Long taskId) {
        return runningTasks.get(taskId);
    }

    // ── 直接搬入的具体方法（无领域差异）─────────────────────────────

    protected String serializeCheckLogs(List<String> logs) {
        try {
            return objectMapper.writeValueAsString(logs == null ? List.of() : logs);
        } catch (Exception e) {
            log.warn("Failed to serialize check logs", e);
            return "[]";
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
            return new ArrayList<>();
        }
    }

    protected void writeCheckLogs(T task, List<String> logs) {
        if (task == null) return;
        try {
            task.setCheckLogsJson(objectMapper.writeValueAsString(logs == null ? List.of() : logs));
        } catch (Exception e) {
            log.warn("Failed to serialize check logs for {} {}", taskResourceType, task.getId(), e);
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
    protected void updateTaskProgress(Long taskId, int progress, String message) {
        Long requiredTaskId = Objects.requireNonNull(taskId, "taskId must not be null");
        int clamped = Math.min(100, Math.max(0, progress));
        taskProgress.put(requiredTaskId, clamped);
        atomicUpdateProgress(requiredTaskId, clamped);
        log.debug("{} {} progress: {}% - {}", taskResourceType, requiredTaskId, progress, message);
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
        Integer progress = taskProgress.get(taskId);
        if (progress != null) {
            return progress;
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
     * <p><b>语义保真</b>：先归属校验 → 原子 DB cancel → updated==0 返回 false。
     *
     * <p>逻辑来源：VerificationServiceImpl:L504-529, SimulationServiceImpl:L298-321
     */
    protected boolean cancelTask(Long userId, Long taskId) {
        T task = findTaskByIdAndUserId(taskId, userId).orElse(null);
        if (task == null) return false;

        int updated = atomicCancelTask(taskId, LocalDateTime.now());
        if (updated == 0) {
            return false;
        }

        cancelledTasks.add(taskId);
        Thread taskThread = runningTasks.get(taskId);
        if (taskThread != null && taskThread.isAlive()) {
            taskThread.interrupt();
        } else {
            cancelledTasks.remove(taskId);
        }

        return true;
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
    protected abstract int atomicUpdateProgress(Long taskId, int progress);
}
