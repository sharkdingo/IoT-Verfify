package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzExplorationMode;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzOutcome;
import cn.edu.nju.Iot_Verify.dto.model.TaskProgressStage;
import cn.edu.nju.Iot_Verify.po.FuzzFindingPo;
import cn.edu.nju.Iot_Verify.po.FuzzTaskPo;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.repository.projection.FuzzFindingSummaryProjection;
import cn.edu.nju.Iot_Verify.repository.projection.FuzzTaskSummaryProjection;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.jdbc.AutoConfigureTestDatabase;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;
import org.springframework.data.domain.PageRequest;

import java.time.LocalDateTime;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

@DataJpaTest(properties = {
        "spring.jpa.database-platform=org.hibernate.dialect.H2Dialect",
        "spring.jpa.properties.hibernate.dialect=org.hibernate.dialect.H2Dialect",
        "spring.jpa.hibernate.ddl-auto=create-drop"
})
@AutoConfigureTestDatabase(replace = AutoConfigureTestDatabase.Replace.ANY)
class FuzzRepositoryTest {

    @Autowired private FuzzTaskRepository taskRepository;
    @Autowired private FuzzFindingRepository findingRepository;
    @Autowired private ChatSessionRepository chatSessionRepository;
    @Autowired private ChatMessageRepository chatMessageRepository;

    @Test
    void currentDatabaseTimeProvidesTheSharedLeaseClock() {
        LocalDateTime before = LocalDateTime.now().minusSeconds(2);
        LocalDateTime databaseTime = taskRepository.currentDatabaseTime();
        LocalDateTime after = LocalDateTime.now().plusSeconds(2);

        assertTrue(!databaseTime.isBefore(before) && !databaseTime.isAfter(after));
    }

    @Test
    void accountCleanupBulkDeleteFlushesPendingDerivedDeletesBeforeClearingPersistenceContext() {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("account-cleanup-session");
        session.setUserId(71L);
        chatSessionRepository.saveAndFlush(session);

        ChatMessagePo message = new ChatMessagePo();
        message.setSessionId(session.getId());
        message.setRole("user");
        message.setContent("pending removal");
        chatMessageRepository.saveAndFlush(message);

        findingRepository.saveAndFlush(FuzzFindingPo.builder()
                .userId(71L)
                .fuzzTaskId(901L)
                .violatedSpecId("spec-cleanup")
                .violatedSpecJson("{}")
                .firstViolationStep(0)
                .statesJson("[]")
                .inputEventsJson("[]")
                .seed(1L)
                .stateCount(0)
                .createdAt(LocalDateTime.now())
                .build());

        chatMessageRepository.deleteBySessionIdIn(List.of(session.getId()));
        chatSessionRepository.deleteByUserId(71L);
        assertEquals(1, findingRepository.deleteByUserId(71L));

        assertTrue(chatMessageRepository.findBySessionIdOrderByCreatedAtAsc(session.getId()).isEmpty());
        assertTrue(chatSessionRepository.findByIdAndUserId(session.getId(), 71L).isEmpty());
    }

    @Test
    void terminalTransitionsAreAtomicAndFindingsRemainUserScoped() {
        LocalDateTime leaseExpiresAt = LocalDateTime.now().plusMinutes(2);
        FuzzTaskPo task = taskRepository.save(FuzzTaskPo.builder()
                .userId(11L)
                .status(FuzzTaskPo.TaskStatus.PENDING)
                .createdAt(LocalDateTime.now())
                .progress(0)
                .targetSpecIdsJson("[]")
                .maxIterations(100)
                .pathLength(10)
                .populationSize(5)
                .modelInputSnapshotJson("{}")
                .modelSnapshotJson("{}")
                .workerId("worker-a")
                .leaseExpiresAt(leaseExpiresAt)
                .build());

        assertEquals(1, taskRepository.startTaskIfStillPending(
                task.getId(), FuzzTaskPo.TaskStatus.RUNNING, LocalDateTime.now(),
                "worker-a", leaseExpiresAt, "[]",
                FuzzTaskPo.TaskStatus.PENDING));
        assertEquals(1, taskRepository.updateProgressIfActive(
                task.getId(), 50, TaskProgressStage.EXPLORING_CANDIDATES));
        FuzzTaskPo taskWithProgress = taskRepository.findById(task.getId()).orElseThrow();
        assertEquals(50, taskWithProgress.getProgress());
        assertEquals(TaskProgressStage.EXPLORING_CANDIDATES, taskWithProgress.getProgressStage());
        assertEquals(1, taskRepository.completeTaskIfRunning(
                task.getId(), FuzzTaskPo.TaskStatus.COMPLETED, LocalDateTime.now(), 10L,
                FuzzOutcome.BUDGET_EXHAUSTED, 7L, 100, 500L, 10L,
                "{\"eligibleSpecIds\":[],\"ineligibleSpecs\":[],\"requestedSpecCount\":0,\"eligibleSpecCount\":0}",
                "[]", 0, "[]", FuzzTaskPo.TaskStatus.RUNNING));
        assertEquals(0, taskRepository.cancelTaskIfStillActive(
                task.getId(), FuzzTaskPo.TaskStatus.CANCELLED, LocalDateTime.now(),
                List.of(FuzzTaskPo.TaskStatus.PENDING, FuzzTaskPo.TaskStatus.RUNNING)));
        assertEquals(0, taskRepository.updateProgressIfActive(
                task.getId(), 50, TaskProgressStage.EXPLORING_CANDIDATES));
        assertEquals(FuzzExplorationMode.BOARD_SNAPSHOT,
                taskRepository.findById(task.getId()).orElseThrow().getExplorationMode());

        FuzzTaskPo cancelledTask = taskRepository.save(FuzzTaskPo.builder()
                .userId(11L)
                .status(FuzzTaskPo.TaskStatus.PENDING)
                .createdAt(LocalDateTime.now())
                .progress(0)
                .explorationMode(FuzzExplorationMode.PAPER_COMPATIBLE)
                .targetSpecIdsJson("[]")
                .maxIterations(100)
                .pathLength(10)
                .populationSize(5)
                .modelInputSnapshotJson("{}")
                .modelSnapshotJson("{}")
                .workerId("worker-a")
                .leaseExpiresAt(leaseExpiresAt)
                .build());
        assertEquals(1, taskRepository.cancelTaskIfStillActive(
                cancelledTask.getId(), FuzzTaskPo.TaskStatus.CANCELLED, LocalDateTime.now(),
                List.of(FuzzTaskPo.TaskStatus.PENDING, FuzzTaskPo.TaskStatus.RUNNING)));
        assertEquals(0, taskRepository.failTaskIfActive(
                cancelledTask.getId(), FuzzTaskPo.TaskStatus.FAILED, LocalDateTime.now(), 1L,
                "late failure", "[]",
                List.of(FuzzTaskPo.TaskStatus.PENDING, FuzzTaskPo.TaskStatus.RUNNING)));
        assertEquals(0, taskRepository.completeTaskIfRunning(
                cancelledTask.getId(), FuzzTaskPo.TaskStatus.COMPLETED, LocalDateTime.now(), 1L,
                FuzzOutcome.BUDGET_EXHAUSTED, 7L, 1, 1L, 1L,
                "{\"eligibleSpecIds\":[],\"ineligibleSpecs\":[],\"requestedSpecCount\":0,\"eligibleSpecCount\":0}",
                "[]", 0, "[]", FuzzTaskPo.TaskStatus.RUNNING));
        assertEquals(FuzzExplorationMode.PAPER_COMPATIBLE,
                taskRepository.findById(cancelledTask.getId()).orElseThrow().getExplorationMode());

        findingRepository.save(FuzzFindingPo.builder()
                .userId(11L)
                .fuzzTaskId(task.getId())
                .violatedSpecId("spec-1")
                .violatedSpecJson("{}")
                .firstViolationStep(2)
                .statesJson("[]")
                .inputEventsJson("[]")
                .seed(7L)
                .stateCount(0)
                .createdAt(LocalDateTime.now())
                .build());

        assertEquals(1, findingRepository
                .findByUserIdAndFuzzTaskIdOrderByCreatedAtAscIdAsc(11L, task.getId()).size());
        assertTrue(findingRepository
                .findByUserIdAndFuzzTaskIdOrderByCreatedAtAscIdAsc(12L, task.getId()).isEmpty());
        List<FuzzTaskPo> completedRuns = taskRepository.findByUserIdAndStatusOrderByCreatedAtDescIdDesc(
                11L, FuzzTaskPo.TaskStatus.COMPLETED, PageRequest.of(0, 25));
        assertEquals(1, completedRuns.size());
        assertEquals(FuzzExplorationMode.BOARD_SNAPSHOT,
                completedRuns.get(0).getExplorationMode());
        List<FuzzTaskPo> inbox = taskRepository.findByUserIdAndStatusNotOrderByCreatedAtDescIdDesc(
                11L, FuzzTaskPo.TaskStatus.COMPLETED, PageRequest.of(0, 100));
        assertEquals(List.of(cancelledTask.getId()), inbox.stream().map(FuzzTaskPo::getId).toList());
        assertEquals(FuzzExplorationMode.PAPER_COMPATIBLE,
                inbox.get(0).getExplorationMode());
    }

    @Test
    void leaseMaintenanceRenewsOnlyItsOwnTasksAndRecoversOnlyExpiredTasks() {
        LocalDateTime now = LocalDateTime.now();
        FuzzTaskPo owned = taskRepository.save(taskForLease("worker-a", now.plusMinutes(1)));
        FuzzTaskPo otherLive = taskRepository.save(taskForLease("worker-b", now.plusMinutes(1)));
        FuzzTaskPo expired = taskRepository.save(taskForLease("worker-dead", now.minusSeconds(1)));

        assertEquals(1, taskRepository.renewOwnedActiveLease(
                owned.getId(), "worker-a", now.plusMinutes(2),
                List.of(FuzzTaskPo.TaskStatus.PENDING, FuzzTaskPo.TaskStatus.RUNNING)));
        assertEquals(1, taskRepository.failExpiredActiveTasks(
                FuzzTaskPo.TaskStatus.FAILED,
                now,
                "Worker lease expired",
                "[]",
                List.of(FuzzTaskPo.TaskStatus.PENDING, FuzzTaskPo.TaskStatus.RUNNING),
                now));

        assertEquals(FuzzTaskPo.TaskStatus.PENDING,
                taskRepository.findById(owned.getId()).orElseThrow().getStatus());
        assertEquals(FuzzTaskPo.TaskStatus.PENDING,
                taskRepository.findById(otherLive.getId()).orElseThrow().getStatus());
        assertEquals(FuzzTaskPo.TaskStatus.FAILED,
                taskRepository.findById(expired.getId()).orElseThrow().getStatus());
    }

    @Test
    void admissionCountsOnlyActiveTasksAndDeletesOnlyOwnedUndispatchedRows() {
        LocalDateTime lease = LocalDateTime.now().plusMinutes(2);
        FuzzTaskPo pending = taskForLease("worker-a", lease);
        pending.setUserId(31L);
        pending = taskRepository.save(pending);
        FuzzTaskPo running = taskForLease("worker-a", lease);
        running.setUserId(31L);
        running.setStatus(FuzzTaskPo.TaskStatus.RUNNING);
        taskRepository.save(running);
        FuzzTaskPo completed = taskForLease("worker-a", lease);
        completed.setUserId(31L);
        completed.setStatus(FuzzTaskPo.TaskStatus.COMPLETED);
        completed = taskRepository.save(completed);
        FuzzTaskPo otherUser = taskForLease("worker-a", lease);
        otherUser.setUserId(32L);
        taskRepository.save(otherUser);

        List<FuzzTaskPo.TaskStatus> active = List.of(
                FuzzTaskPo.TaskStatus.PENDING, FuzzTaskPo.TaskStatus.RUNNING);
        assertEquals(3L, taskRepository.countByUserId(31L));
        assertEquals(1L, taskRepository.countByUserId(32L));
        assertEquals(2L, taskRepository.countByUserIdAndStatusIn(31L, active));
        assertEquals(0, taskRepository.deleteUndispatchedTask(
                pending.getId(), 31L, "worker-b", FuzzTaskPo.TaskStatus.PENDING));
        assertEquals(0, taskRepository.deleteUndispatchedTask(
                completed.getId(), 31L, "worker-a", FuzzTaskPo.TaskStatus.PENDING));
        assertEquals(1, taskRepository.deleteUndispatchedTask(
                pending.getId(), 31L, "worker-a", FuzzTaskPo.TaskStatus.PENDING));
        assertTrue(taskRepository.findById(pending.getId()).isEmpty());
        assertTrue(taskRepository.findById(completed.getId()).isPresent());
        assertEquals(2L, taskRepository.countByUserId(31L));
    }

    @Test
    void listProjectionsDoNotExposeFrozenInputOrFindingEvidenceColumns() {
        LocalDateTime now = LocalDateTime.now();
        FuzzTaskPo task = taskRepository.saveAndFlush(FuzzTaskPo.builder()
                .userId(21L)
                .status(FuzzTaskPo.TaskStatus.COMPLETED)
                .createdAt(now)
                .completedAt(now.plusSeconds(1))
                .progress(100)
                .targetSpecIdsJson("[]")
                .maxIterations(1)
                .pathLength(1)
                .populationSize(1)
                .modelInputSnapshotJson("{\"large\":\"frozen\"}")
                .modelSnapshotJson("{\"capturedAt\":\"2026-07-15T00:00:00\",\"templatesFrozen\":true}")
                .outcome(FuzzOutcome.BUDGET_EXHAUSTED)
                .effectiveSeed(1L)
                .iterations(1)
                .generatedPaths(1L)
                .elapsedMs(1L)
                .eligibilityJson("{\"eligibleSpecIds\":[],\"eligibleSpecLabels\":{},\"ineligibleSpecs\":[],\"requestedSpecCount\":0,\"eligibleSpecCount\":0}")
                .limitationsJson("[]")
                .findingCount(0)
                .build());

        List<FuzzTaskSummaryProjection> tasks = taskRepository
                .findSummaryByUserIdAndStatusOrderByCreatedAtDescIdDesc(
                        21L, FuzzTaskPo.TaskStatus.COMPLETED, PageRequest.of(0, 10));

        assertEquals(List.of(task.getId()), tasks.stream().map(FuzzTaskSummaryProjection::getId).toList());
        assertTrue(Arrays.stream(FuzzTaskSummaryProjection.class.getMethods())
                .map(Method::getName)
                .noneMatch(name -> name.equals("getModelInputSnapshotJson")
                        || name.equals("getCheckLogsJson")));
        assertTrue(Arrays.stream(FuzzFindingSummaryProjection.class.getMethods())
                .map(Method::getName)
                .noneMatch(name -> name.equals("getViolatedSpecJson")
                        || name.equals("getStatesJson")
                        || name.equals("getInputEventsJson")));
    }

    private FuzzTaskPo taskForLease(String workerId, LocalDateTime leaseExpiresAt) {
        return FuzzTaskPo.builder()
                .userId(11L)
                .status(FuzzTaskPo.TaskStatus.PENDING)
                .createdAt(LocalDateTime.now())
                .progress(0)
                .targetSpecIdsJson("[]")
                .maxIterations(1)
                .pathLength(1)
                .populationSize(1)
                .modelInputSnapshotJson("{}")
                .modelSnapshotJson("{}")
                .workerId(workerId)
                .leaseExpiresAt(leaseExpiresAt)
                .build();
    }
}
