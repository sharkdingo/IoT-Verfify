package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.model.TaskCancellationOutcome;
import cn.edu.nju.Iot_Verify.dto.model.TaskCancellationResultDto;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.po.TaskView;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import java.time.LocalDateTime;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

class AbstractAsyncTaskServiceCancelTest {

    private static class TestTask implements TaskView {
        private final Long id;
        private final Long userId;
        private boolean cancelled;
        private boolean terminal;
        private Integer progress;
        private String checkLogsJson;

        private TestTask(Long id, Long userId) {
            this.id = id;
            this.userId = userId;
        }

        @Override
        public Long getId() {
            return id;
        }

        @Override
        public Integer getProgress() {
            return progress;
        }

        @Override
        public boolean isTerminalStatus() {
            return terminal || cancelled;
        }

        @Override
        public boolean isCancelledStatus() {
            return cancelled;
        }

        @Override
        public String getTaskStatusName() {
            if (cancelled) return "CANCELLED";
            if (terminal) return "COMPLETED";
            return "PENDING";
        }

        @Override
        public String getCheckLogsJson() {
            return checkLogsJson;
        }

        @Override
        public void setCheckLogsJson(String json) {
            this.checkLogsJson = json;
        }
    }

    private static class TestAsyncTaskService extends AbstractAsyncTaskService<TestTask> {
        private final TestTask task = new TestTask(7L, 1L);
        private int cancelUpdateResult = 1;
        private boolean setCancelledDuringAtomicCancel;
        private boolean markerVisibleDuringAtomicCancel;

        private TestAsyncTaskService() {
            super(new ObjectMapper(), "TestTask");
        }

        private TaskCancellationResultDto cancel(Long userId, Long taskId) {
            return cancelTask(userId, taskId);
        }

        private boolean hasCancelMarker(Long taskId) {
            return isTaskCancelled(taskId);
        }

        @Override
        protected Optional<TestTask> findTaskByIdAndUserId(Long id, Long userId) {
            return task.id.equals(id) && task.userId.equals(userId)
                    ? Optional.of(task)
                    : Optional.empty();
        }

        @Override
        protected int atomicCancelTask(Long taskId, LocalDateTime completedAt) {
            markerVisibleDuringAtomicCancel = isTaskCancelled(taskId);
            if (setCancelledDuringAtomicCancel || cancelUpdateResult == 1) {
                task.cancelled = true;
                task.terminal = true;
            }
            return cancelUpdateResult;
        }

        @Override
        protected int atomicUpdateProgress(Long taskId, int progress) {
            task.progress = progress;
            return 1;
        }
    }

    @Test
    void cancelTask_marksInMemoryBeforeAtomicDbCancel() {
        TestAsyncTaskService service = new TestAsyncTaskService();

        TaskCancellationResultDto result = service.cancel(1L, 7L);

        assertTrue(result.isCancellationAccepted());
        assertEquals(TaskCancellationOutcome.ACCEPTED, result.getCancellationOutcome());
        assertEquals("CANCELLED", result.getTaskStatus());
        assertTrue(service.markerVisibleDuringAtomicCancel);
        assertFalse(service.hasCancelMarker(7L), "marker should be cleared when no local worker owns the task");
    }

    @Test
    void cancelTask_returnsTrueWhenWorkerAlreadyCancelledTask() {
        TestAsyncTaskService service = new TestAsyncTaskService();
        service.cancelUpdateResult = 0;
        service.setCancelledDuringAtomicCancel = true;

        TaskCancellationResultDto result = service.cancel(1L, 7L);

        assertFalse(result.isCancellationAccepted());
        assertEquals(TaskCancellationOutcome.ALREADY_CANCELLED, result.getCancellationOutcome());
        assertTrue(service.markerVisibleDuringAtomicCancel);
        assertFalse(service.hasCancelMarker(7L), "terminal cancelled task should not leave a stale marker");
    }

    @Test
    void cancelTask_returnsFalseAndClearsMarkerWhenTaskAlreadyCompleted() {
        TestAsyncTaskService service = new TestAsyncTaskService();
        service.cancelUpdateResult = 0;
        service.task.terminal = true;

        TaskCancellationResultDto result = service.cancel(1L, 7L);

        assertFalse(result.isCancellationAccepted());
        assertEquals(TaskCancellationOutcome.ALREADY_COMPLETED, result.getCancellationOutcome());
        assertTrue(service.markerVisibleDuringAtomicCancel);
        assertFalse(service.hasCancelMarker(7L), "completed task should not leave a stale cancel marker");
    }

    @Test
    void cancelTask_unknownOrForeignTask_isNotReportedAsGenericFalse() {
        TestAsyncTaskService service = new TestAsyncTaskService();

        assertThrows(ResourceNotFoundException.class, () -> service.cancel(2L, 7L));
    }
}
