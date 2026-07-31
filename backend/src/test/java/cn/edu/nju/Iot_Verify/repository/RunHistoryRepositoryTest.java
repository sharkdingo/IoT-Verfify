package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.dto.verification.VerificationOutcome;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.RunInitiator;
import cn.edu.nju.Iot_Verify.po.SimulationTaskPo;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import cn.edu.nju.Iot_Verify.repository.projection.SimulationTraceSummaryProjection;
import cn.edu.nju.Iot_Verify.repository.projection.SimulationTaskSummaryProjection;
import cn.edu.nju.Iot_Verify.repository.projection.TraceSummaryProjection;
import cn.edu.nju.Iot_Verify.repository.projection.VerificationTaskSummaryProjection;
import cn.edu.nju.Iot_Verify.repository.projection.VerificationRunSummaryProjection;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.jdbc.AutoConfigureTestDatabase;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;
import org.springframework.data.domain.PageRequest;
import org.springframework.data.jpa.repository.Query;

import java.time.LocalDateTime;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;

@DataJpaTest(properties = {
        "spring.jpa.database-platform=org.hibernate.dialect.H2Dialect",
        "spring.jpa.properties.hibernate.dialect=org.hibernate.dialect.H2Dialect",
        "spring.jpa.hibernate.ddl-auto=create-drop"
})
@AutoConfigureTestDatabase(replace = AutoConfigureTestDatabase.Replace.ANY)
class RunHistoryRepositoryTest {

    private static final String NO_ATTACK_SEMANTICS_JSON = JsonUtils.toJson(
            ModelSemanticsDto.forRun(AttackScenarioDto.none(), false, 1, 0, 0));
    private static final String VERIFICATION_SNAPSHOT_JSON =
            "{\"capturedAt\":\"2026-07-24T09:30:00\",\"deviceCount\":1,\"ruleCount\":0,"
                    + "\"specificationCount\":1,\"environmentVariableCount\":0,"
                    + "\"deviceTemplateCount\":1,\"templatesFrozen\":true}";
    private static final String SIMULATION_SNAPSHOT_JSON =
            "{\"capturedAt\":\"2026-07-24T09:30:00\",\"deviceCount\":1,\"ruleCount\":0,"
                    + "\"specificationCount\":0,\"environmentVariableCount\":0,"
                    + "\"deviceTemplateCount\":1,\"templatesFrozen\":true}";

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
                simulationTraceRepository.findSummariesByUserId(
                        7L, PageRequest.of(0, 10));
        assertEquals(List.of(standalone.getId(), taskOwned.getId()),
                summaries.stream().map(SimulationTraceSummaryProjection::getId).toList());
        assertEquals(2, summaries.get(0).getStateCount());
        assertEquals(RunInitiator.AI_ASSISTANT, summaries.get(0).getInitiator());
        assertEquals(NO_ATTACK_SEMANTICS_JSON, summaries.get(0).getModelSemanticsJson());
        assertEquals(1, summaries.get(0).getModeledDeviceAttackPointCount());
    }

    @Test
    void verificationHistoryProjectionsReturnOnlyRequestedRunAndTraceSummaries() {
        LocalDateTime now = LocalDateTime.now();
        VerificationTaskPo run = verificationTaskRepository.saveAndFlush(
                VerificationTaskPo.builder()
                        .userId(9L)
                        .initiator(RunInitiator.AI_ASSISTANT)
                        .status(VerificationTaskPo.TaskStatus.COMPLETED)
                        .createdAt(now)
                        .startedAt(now)
                        .completedAt(now.plusSeconds(1))
                        .isAttack(false)
                        .attackBudget(0)
                        .modeledDeviceAttackPointCount(1)
                        .modeledFalsifiableReadingDeviceCount(0)
                        .modeledAutomationLinkAttackPointCount(0)
                        .enablePrivacy(false)
                        .outcome(VerificationOutcome.VIOLATED)
                        .modelSemanticsJson(NO_ATTACK_SEMANTICS_JSON)
                        .modelSnapshotJson(VERIFICATION_SNAPSHOT_JSON)
                        .generationIssuesJson("[]")
                        .build());
        TracePo trace = traceRepository.saveAndFlush(TracePo.builder()
                .userId(9L)
                .verificationTaskId(run.getId())
                .violatedSpecId("spec-1")
                .violatedSpecJson("{}")
                .statesJson("[{}]")
                .stateCount(1)
                .requestJson("{\"rules\":[]}")
                .isAttack(false)
                .attackBudget(0)
                .enablePrivacy(false)
                .modeledDeviceAttackPointCount(1)
                .modeledFalsifiableReadingDeviceCount(0)
                .modeledAutomationLinkAttackPointCount(0)
                .modelSemanticsJson(NO_ATTACK_SEMANTICS_JSON)
                .modelSnapshotJson(VERIFICATION_SNAPSHOT_JSON)
                .createdAt(now.plusSeconds(1))
                .build());

        List<VerificationRunSummaryProjection> runs =
                verificationTaskRepository.findByUserIdAndStatusOrderByCompletedAtDescIdDesc(
                        9L, VerificationTaskPo.TaskStatus.COMPLETED, PageRequest.of(0, 10));
        List<TraceSummaryProjection> traces =
                traceRepository.findSummariesByUserIdAndVerificationTaskIdIn(
                        9L, List.of(run.getId()));

        assertEquals(List.of(run.getId()),
                runs.stream().map(VerificationRunSummaryProjection::getId).toList());
        assertEquals(RunInitiator.AI_ASSISTANT, runs.get(0).getInitiator());
        assertEquals(List.of(trace.getId()), traces.stream().map(TraceSummaryProjection::getId).toList());
        assertEquals(1, traces.get(0).getStateCount());
    }

    @Test
    void historyAndTaskSummaryQueriesExcludeDetailPayloads() throws Exception {
        Query verificationQuery = TraceRepository.class
                .getMethod("findSummariesByUserIdAndVerificationTaskIdIn", Long.class, List.class)
                .getAnnotation(Query.class);
        Query simulationQuery = SimulationTraceRepository.class
                .getMethod("findSummariesByUserId", Long.class, org.springframework.data.domain.Pageable.class)
                .getAnnotation(Query.class);

        for (Query query : List.of(verificationQuery, simulationQuery)) {
            assertFalse(query.value().contains("statesJson"));
            assertFalse(query.value().contains("requestJson"));
        }

        assertThrows(NoSuchMethodException.class,
                () -> VerificationTaskSummaryProjection.class.getMethod("getNusmvOutput"));
        assertThrows(NoSuchMethodException.class,
                () -> VerificationTaskSummaryProjection.class.getMethod("getSpecResultsJson"));
        assertThrows(NoSuchMethodException.class,
                () -> VerificationTaskSummaryProjection.class.getMethod("getCheckLogsJson"));
        assertThrows(NoSuchMethodException.class,
                () -> SimulationTaskSummaryProjection.class.getMethod("getWorkerId"));
        assertThrows(NoSuchMethodException.class,
                () -> SimulationTaskSummaryProjection.class.getMethod("getLeaseExpiresAt"));
        assertThrows(NoSuchMethodException.class,
                () -> TraceRepository.class.getMethod(
                        "findByUserIdOrderByCreatedAtDesc", Long.class));
    }

    private SimulationTracePo simulationTrace(Long userId, LocalDateTime createdAt) {
        return SimulationTracePo.builder()
                .userId(userId)
                .initiator(RunInitiator.AI_ASSISTANT)
                .requestedSteps(3)
                .steps(1)
                .statesJson("[{},{}]")
                .stateCount(2)
                .logsJson("[]")
                .generationIssuesJson("[]")
                .requestJson("{\"rules\":[]}")
                .isAttack(false)
                .attackBudget(0)
                .enablePrivacy(false)
                .modeledDeviceAttackPointCount(1)
                .modeledFalsifiableReadingDeviceCount(0)
                .modeledAutomationLinkAttackPointCount(0)
                .modelSemanticsJson(NO_ATTACK_SEMANTICS_JSON)
                .modelSnapshotJson(SIMULATION_SNAPSHOT_JSON)
                .createdAt(createdAt)
                .build();
    }
}
