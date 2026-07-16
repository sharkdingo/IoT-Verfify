package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.dto.model.InteractiveOperationStage;
import cn.edu.nju.Iot_Verify.dto.model.InteractiveOperationStatusDto;
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

/** Request-scoped cancellation for bounded automatic-fix searches. */
@Service
public class InteractiveFixExecutionService {

    private final ThreadPoolTaskExecutor executor;
    private final Map<RequestKey, ActiveExecution<?>> active = new ConcurrentHashMap<>();

    public InteractiveFixExecutionService(
            @Qualifier("syncVerificationExecutor") ThreadPoolTaskExecutor executor) {
        this.executor = executor;
    }

    public <T> T execute(Long userId, String requestId, Callable<T> operation) {
        String id = validateRequestId(requestId);
        RequestKey key = new RequestKey(userId, id);
        ActiveExecution<T> execution = new ActiveExecution<>(key, operation);
        if (active.putIfAbsent(key, execution) != null) {
            throw new BadRequestException("A fix request with this requestId is already active.");
        }
        try {
            executor.execute(execution.task);
            return execution.task.get();
        } catch (RejectedExecutionException e) {
            execution.cancel();
            throw new ServiceUnavailableException("Automatic-fix capacity is currently full.", e);
        } catch (CancellationException e) {
            throw new ServiceUnavailableException("Automatic-fix search was cancelled.", e);
        } catch (InterruptedException e) {
            execution.cancel();
            Thread.currentThread().interrupt();
            throw new ServiceUnavailableException("Automatic-fix search was interrupted.", e);
        } catch (ExecutionException e) {
            Throwable cause = e.getCause();
            if (cause instanceof RuntimeException runtime) throw runtime;
            throw new ServiceUnavailableException("Automatic-fix search failed.", cause);
        } finally {
            if (executor.getThreadPoolExecutor() != null) executor.getThreadPoolExecutor().purge();
        }
    }

    public boolean cancel(Long userId, String requestId) {
        ActiveExecution<?> execution = active.get(new RequestKey(userId, validateRequestId(requestId)));
        return execution != null && execution.cancel();
    }

    public InteractiveOperationStatusDto getStatus(Long userId, String requestId) {
        String id = validateRequestId(requestId);
        ActiveExecution<?> execution = active.get(new RequestKey(userId, id));
        if (execution == null) {
            throw new ResourceNotFoundException("automatic-fix request", id);
        }
        return execution.status();
    }

    public void markStage(Long userId, String requestId, InteractiveOperationStage stage) {
        ActiveExecution<?> execution = active.get(new RequestKey(userId, validateRequestId(requestId)));
        if (execution != null) execution.stage.set(Objects.requireNonNull(stage));
    }

    private String validateRequestId(String requestId) {
        String value = requestId == null ? "" : requestId.trim();
        if (!value.matches("[A-Za-z0-9_-]{8,80}")) {
            throw new BadRequestException("requestId must contain 8-80 URL-safe characters.");
        }
        return value;
    }

    private record RequestKey(Long userId, String requestId) {
    }

    private enum ExecutionState {
        WAITING,
        RUNNING,
        FINISHED
    }

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
                    throw new CancellationException("Automatic-fix search was cancelled before it started.");
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
            active.remove(key, this);
        }
    }
}
