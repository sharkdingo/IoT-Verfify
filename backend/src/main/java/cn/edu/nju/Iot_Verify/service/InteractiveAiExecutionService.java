package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import cn.edu.nju.Iot_Verify.dto.model.InteractiveOperationStage;
import cn.edu.nju.Iot_Verify.dto.model.InteractiveOperationStatusDto;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Qualifier;
import org.springframework.scheduling.concurrent.ThreadPoolTaskExecutor;
import org.springframework.stereotype.Service;

import java.util.Map;
import java.util.Objects;
import java.util.concurrent.Callable;
import java.util.concurrent.CancellationException;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ExecutionException;
import java.util.concurrent.FutureTask;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;

/** Bounded, user-cancellable execution for synchronous AI recommendation endpoints. */
@Slf4j
@Service
public class InteractiveAiExecutionService {

    private static final long COMPLETED_STATUS_TTL_NANOS = TimeUnit.SECONDS.toNanos(15);

    private final ThreadPoolTaskExecutor executor;
    private final Map<RequestKey, ActiveExecution<?>> active = new ConcurrentHashMap<>();
    private final Map<Long, String> activeByUser = new ConcurrentHashMap<>();
    private final Map<RequestKey, RecentStatus> recentlyCompleted = new ConcurrentHashMap<>();

    public InteractiveAiExecutionService(
            @Qualifier("interactiveAiExecutor") ThreadPoolTaskExecutor executor) {
        this.executor = executor;
    }

    public <T> T execute(Long userId, String requestId, Callable<T> operation) {
        purgeExpiredStatuses();
        String id = validateRequestId(requestId);
        RequestKey key = new RequestKey(userId, id);
        String existing = activeByUser.putIfAbsent(userId, id);
        if (existing != null) {
            throw new ServiceUnavailableException(
                    "Another AI recommendation is already running for this user. Stop it before starting a new one.");
        }

        ActiveExecution<T> execution = new ActiveExecution<>(key, operation);
        if (active.putIfAbsent(key, execution) != null) {
            activeByUser.remove(userId, id);
            throw new ServiceUnavailableException(
                    "An AI recommendation with this requestId is already running.");
        }
        try {
            executor.execute(execution.task);
            return execution.task.get();
        } catch (RejectedExecutionException e) {
            execution.cancel();
            throw new ServiceUnavailableException(
                    "AI recommendation capacity is currently full. Try again shortly.", e);
        } catch (CancellationException e) {
            throw new ServiceUnavailableException("AI recommendation was cancelled.", e);
        } catch (InterruptedException e) {
            execution.cancel();
            Thread.currentThread().interrupt();
            throw new ServiceUnavailableException("AI recommendation was interrupted.", e);
        } catch (ExecutionException e) {
            Throwable cause = e.getCause();
            if (cause instanceof RuntimeException runtime) throw runtime;
            throw new ServiceUnavailableException("AI recommendation failed.", cause);
        } finally {
            if (executor.getThreadPoolExecutor() != null) executor.getThreadPoolExecutor().purge();
        }
    }

    public boolean cancel(Long userId, String requestId) {
        String id = validateRequestId(requestId);
        ActiveExecution<?> execution = active.get(new RequestKey(userId, id));
        boolean cancelled = execution != null && execution.cancel();
        log.info("AI recommendation cancellation: userId={}, requestId={}, cancelled={}",
                userId, id, cancelled);
        return cancelled;
    }

    public InteractiveOperationStatusDto getStatus(Long userId, String requestId) {
        purgeExpiredStatuses();
        String id = validateRequestId(requestId);
        RequestKey key = new RequestKey(userId, id);
        ActiveExecution<?> execution = active.get(key);
        if (execution != null) return execution.status();
        RecentStatus recent = recentlyCompleted.get(key);
        if (recent != null) return recent.status();
        throw new ResourceNotFoundException("AI recommendation request", id);
    }

    public void markStage(Long userId, String requestId, InteractiveOperationStage stage) {
        ActiveExecution<?> execution = active.get(new RequestKey(userId, validateRequestId(requestId)));
        if (execution != null) execution.stage.set(Objects.requireNonNull(stage));
    }

    private String validateRequestId(String requestId) {
        String value = requestId == null ? "" : requestId.trim();
        if (value.length() < RequestLimits.MIN_REQUEST_ID_LENGTH
                || value.length() > RequestLimits.MAX_REQUEST_ID_LENGTH
                || !value.matches(RequestLimits.REQUEST_ID_PATTERN)) {
            throw new BadRequestException("requestId must contain 8-80 characters and use only letters, digits, ., _, :, or -.");
        }
        return value;
    }

    private record RequestKey(Long userId, String requestId) {
    }

    private record RecentStatus(InteractiveOperationStatusDto status, long expiresAtNanos) {
    }

    private void purgeExpiredStatuses() {
        long now = System.nanoTime();
        recentlyCompleted.forEach((key, recent) -> {
            if (recent.expiresAtNanos() <= now) recentlyCompleted.remove(key, recent);
        });
    }

    private enum ExecutionState {
        WAITING,
        RUNNING,
        FINISHED
    }

    /**
     * FutureTask reports cancellation before an interrupt-ignoring provider call has returned.
     * Keep the request registered until the callable actually exits so per-user admission remains
     * truthful and repeated stop/retry actions cannot stack hidden model work.
     */
    private final class ActiveExecution<T> {
        private final RequestKey key;
        private final AtomicReference<ExecutionState> state =
                new AtomicReference<>(ExecutionState.WAITING);
        private final AtomicBoolean cleaned = new AtomicBoolean(false);
        private final AtomicReference<InteractiveOperationStage> stage =
                new AtomicReference<>(InteractiveOperationStage.QUEUED);
        private final long createdAtNanos = System.nanoTime();
        private final FutureTask<T> task;

        private ActiveExecution(RequestKey key, Callable<T> operation) {
            this.key = key;
            this.task = new FutureTask<>(() -> {
                if (!state.compareAndSet(ExecutionState.WAITING, ExecutionState.RUNNING)) {
                    throw new CancellationException("AI recommendation was cancelled before it started.");
                }
                stage.compareAndSet(InteractiveOperationStage.QUEUED, InteractiveOperationStage.RUNNING);
                try {
                    return operation.call();
                } finally {
                    state.set(ExecutionState.FINISHED);
                    cleanup();
                }
            });
        }

        private boolean cancel() {
            stage.set(InteractiveOperationStage.CANCELLING);
            boolean cancelled = task.cancel(true);
            if (cancelled && state.compareAndSet(ExecutionState.WAITING, ExecutionState.FINISHED)) {
                cleanup();
            }
            return cancelled;
        }

        private InteractiveOperationStatusDto status() {
            return InteractiveOperationStatusDto.builder()
                    .requestId(key.requestId())
                    .state(state.get().name())
                    .stage(stage.get())
                    .elapsedMs(TimeUnit.NANOSECONDS.toMillis(System.nanoTime() - createdAtNanos))
                    .build();
        }

        private void cleanup() {
            if (!cleaned.compareAndSet(false, true)) return;
            recentlyCompleted.put(key, new RecentStatus(
                    status(), System.nanoTime() + COMPLETED_STATUS_TTL_NANOS));
            active.remove(key, this);
            activeByUser.remove(key.userId(), key.requestId());
        }
    }
}
