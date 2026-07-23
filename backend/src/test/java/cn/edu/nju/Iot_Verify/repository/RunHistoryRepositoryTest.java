package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.dto.verification.VerificationOutcome;
import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import cn.edu.nju.Iot_Verify.repository.projection.SimulationTraceSummaryProjection;
import cn.edu.nju.Iot_Verify.repository.projection.TraceSummaryProjection;
import cn.edu.nju.Iot_Verify.repository.projection.VerificationRunSummaryProjection;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.jdbc.AutoConfigureTestDatabase;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;
import org.springframework.data.domain.PageRequest;

import java.time.LocalDateTime;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

@DataJpaTest(properties = {
        "spring.jpa.database-platform=org.hibernate.dialect.H2Dialect",
        "spring.jpa.properties.hibernate.dialect=org.hibernate.dialect.H2Dialect",
        "spring.jpa.hibernate.ddl-auto=create-drop"
})
@AutoConfigureTestDatabase(replace = AutoConfigureTestDatabase.Replace.ANY)
class RunHistoryRepositoryTest {

    @Autowired private SimulationTraceRepository simulationTraceRepository;
    @Autowired private SimulationTaskRepository simulationTaskRepository;
    @Autowired private VerificationTaskRepository verificationTaskRepository;
    @Autowired private TraceRepository traceRepository;

    @Test
    void simulationStoredRunCountDoesNotDoubleCountTaskOwnedTrace() {
        LocalDateTime now = LocalDateTime.now();
        SimulationTracePo taskOwned = simulationTraceRepository.saveAndFlush(simulationTrace(7L, now));
        SimulationTracePo standalone = simulationTraceRepository.saveAndFlush(
                simulationTrace(7L, now.plusSeconds(1)));
        simulationTaskRepository.saveAndFlush(SimulationTaskPo.builder()
                .userId(7L)
                .status(SimulationTaskPo.TaskStatus.COMPLETED)
                .createdAt(now)
                .completedAt(now)
                .simulationTraceId(taskOwned.getId())
                .build());

        assertEquals(1L, simulationTaskRepository.countByUserId(7L));
        assertEquals(1L, simulationTraceRepository.countStandaloneByUserId(7L));
        List<SimulationTraceSummaryProjection> summaries =
                simulationTraceRepository.findByUserIdOrderByCreatedAtDescIdDesc(
                        7L, PageRequest.of(0, 10));
        assertEquals(List.of(standalone.getId(), taskOwned.getId()),
                summaries.stream().map(SimulationTraceSummaryProjection::getId).toList());
        assertEquals(2, summaries.get(0).getStateCount());
    }

    @Test
    void verificationHistoryProjectionsReturnOnlyRequestedRunAndTraceSummaries() {
        LocalDateTime now = LocalDateTime.now();
        VerificationTaskPo run = verificationTaskRepository.saveAndFlush(
                VerificationTaskPo.builder()
                        .userId(9L)
                        .status(VerificationTaskPo.TaskStatus.COMPLETED)
                        .createdAt(now)
                        .startedAt(now)
                        .completedAt(now.plusSeconds(1))
                        .outcome(VerificationOutcome.VIOLATED)
                        .modelSnapshotJson("{}")
                        .generationIssuesJson("[]")
                        .build());
        TracePo trace = traceRepository.saveAndFlush(TracePo.builder()
                .userId(9L)
                .verificationTaskId(run.getId())
                .violatedSpecId("spec-1")
                .violatedSpecJson("{}")
                .statesJson("[{}]")
                .stateCount(1)
                .createdAt(now.plusSeconds(1))
                .build());

        List<VerificationRunSummaryProjection> runs =
                verificationTaskRepository.findByUserIdAndStatusOrderByCompletedAtDescIdDesc(
                        9L, VerificationTaskPo.TaskStatus.COMPLETED, PageRequest.of(0, 10));
        List<TraceSummaryProjection> traces =
                traceRepository.findByUserIdAndVerificationTaskIdInOrderByCreatedAtDesc(
                        9L, List.of(run.getId()));

        assertEquals(List.of(run.getId()),
                runs.stream().map(VerificationRunSummaryProjection::getId).toList());
        assertEquals(List.of(trace.getId()), traces.stream().map(TraceSummaryProjection::getId).toList());
        assertEquals(1, traces.get(0).getStateCount());
    }

    private SimulationTracePo simulationTrace(Long userId, LocalDateTime createdAt) {
        return SimulationTracePo.builder()
                .userId(userId)
                .requestedSteps(3)
                .steps(1)
                .statesJson("[{},{}]")
                .stateCount(2)
                .logsJson("[]")
                .generationIssuesJson("[]")
                .modelSnapshotJson("{}")
                .createdAt(createdAt)
                .build();
    }
}
