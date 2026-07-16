package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.component.fuzz.FuzzLimitationContract;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzEligibilityDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzExplorationMode;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzInputEventDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzIneligibleSpecDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzOutcome;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzRunDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzRunSummaryDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzTaskDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzTaskSummaryDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.po.FuzzFindingPo;
import cn.edu.nju.Iot_Verify.po.FuzzTaskPo;
import cn.edu.nju.Iot_Verify.repository.projection.FuzzFindingSummaryProjection;
import cn.edu.nju.Iot_Verify.repository.projection.FuzzTaskSummaryProjection;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import org.junit.jupiter.api.Test;

import java.time.LocalDateTime;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

class FuzzMapperTest {

    private final FuzzMapper mapper = new FuzzMapper();

    @Test
    void mapsCompletedRunAndEmbedsFindingSummaries() {
        LocalDateTime createdAt = LocalDateTime.of(2026, 7, 14, 9, 30);
        SpecificationDto specification = supportedSpecification("spec-1");
        specification.setTemplateLabel("Never unlock while away");
        TraceStateDto state = TraceStateDto.builder()
                .stateIndex(0)
                .devices(List.of())
                .triggeredRules(List.of())
                .compromisedAutomationLinks(List.of())
                .build();
        FuzzFindingPo finding = FuzzFindingPo.builder()
                .id(9L)
                .userId(3L)
                .fuzzTaskId(7L)
                .violatedSpecId("spec-1")
                .violatedSpecJson(JsonUtils.toJson(specification))
                .firstViolationStep(0)
                .statesJson(JsonUtils.toJson(List.of(state)))
                .inputEventsJson(JsonUtils.toJson(List.of(FuzzInputEventDto.builder()
                        .step(0)
                        .kind("DEVICE_VARIABLE")
                        .targetId("DoorLock")
                        .property("battery")
                        .value("80")
                        .build())))
                .seed(42L)
                .stateCount(1)
                .createdAt(createdAt.plusSeconds(1))
                .build();
        FuzzTaskPo task = FuzzTaskPo.builder()
                .id(7L)
                .userId(3L)
                .status(FuzzTaskPo.TaskStatus.COMPLETED)
                .createdAt(createdAt)
                .completedAt(createdAt.plusSeconds(2))
                .progress(100)
                .targetSpecIdsJson(JsonUtils.toJson(List.of("spec-1")))
                .maxIterations(1000)
                .pathLength(20)
                .populationSize(10)
                .explorationMode(FuzzExplorationMode.PAPER_COMPATIBLE)
                .modelInputSnapshotJson(JsonUtils.toJson(inputSnapshot(List.of(specification))))
                .modelSnapshotJson(JsonUtils.toJson(ModelRunSnapshotDto.captured(
                        createdAt, 0, 0, 1, 0, 0)))
                .outcome(FuzzOutcome.FOUND_VIOLATION)
                .effectiveSeed(42L)
                .iterations(12)
                .generatedPaths(120L)
                .elapsedMs(250L)
                .eligibilityJson(JsonUtils.toJson(FuzzEligibilityDto.builder()
                        .eligibleSpecIds(List.of("spec-1"))
                        .eligibleSpecLabels(Map.of("spec-1", "Never unlock while away"))
                        .requestedSpecCount(1)
                        .eligibleSpecCount(1)
                        .build()))
                .limitationsJson(JsonUtils.toJson(
                        FuzzLimitationContract.requiredCodes(FuzzExplorationMode.PAPER_COMPATIBLE)))
                .findingCount(1)
                .build();

        FuzzRunSummaryDto dto = mapper.toRunSummaryDto(task, List.of(finding));
        FuzzRunDto runDetail = mapper.toRunDto(task, List.of(finding));
        FuzzTaskDto taskDetail = mapper.toTaskDto(task);
        FuzzTaskSummaryDto taskSummary = mapper.toTaskSummaryDto(task);

        assertEquals(FuzzOutcome.FOUND_VIOLATION, dto.getOutcome());
        assertEquals(FuzzExplorationMode.PAPER_COMPATIBLE, dto.getExplorationMode());
        assertEquals(FuzzExplorationMode.PAPER_COMPATIBLE, runDetail.getExplorationMode());
        assertEquals(FuzzExplorationMode.PAPER_COMPATIBLE, taskDetail.getExplorationMode());
        assertEquals(FuzzExplorationMode.PAPER_COMPATIBLE, taskSummary.getExplorationMode());
        assertEquals(42L, dto.getEffectiveSeed());
        assertTrue(dto.isDataAvailable());
        assertEquals(1, dto.getFindingCount());
        assertEquals(1, dto.getFindings().size());
        assertEquals("spec-1", dto.getFindings().get(0).getViolatedSpecId());
        assertEquals(42L, dto.getFindings().get(0).getSeed());
        assertTrue(dto.getFindings().get(0).isDataAvailable());
        assertEquals("MODEL_CHOICE", runDetail.getFindings().get(0)
                .getInputEvents().get(0).getSource());
        assertEquals(0, dto.getModelSnapshot().getDeviceCount());
        assertEquals(0, taskSummary.getModelSnapshot().getDeviceCount());
        assertEquals(List.of("spec-1"), taskSummary.getTargetSpecIds());
        assertEquals(Map.of("spec-1", "Never unlock while away"),
                runDetail.getEligibility().getEligibleSpecLabels());
        assertTrue(runDetail.getLimitations().contains(
                "PAPER_PREDECESSOR_STATE_OUTPUTS_THREE_LEVELS_ONLY"));
        assertTrue(runDetail.getLimitations().contains(
                "PAPER_MULTI_TARGET_PRODUCT_EXTENSION"));
        assertTrue(runDetail.getLimitations().contains(
                "ATTACK_TRUST_PRIVACY_CONTENT_UNSUPPORTED"));
    }

    @Test
    void findingSummaryRejectsInconsistentPersistedTraceMetadata() {
        SpecificationDto specification = supportedSpecification("spec-1");
        TraceStateDto state = TraceStateDto.builder()
                .stateIndex(0)
                .devices(List.of())
                .triggeredRules(List.of())
                .compromisedAutomationLinks(List.of())
                .build();
        FuzzFindingPo finding = FuzzFindingPo.builder()
                .id(10L)
                .userId(3L)
                .fuzzTaskId(7L)
                .violatedSpecId("spec-1")
                .violatedSpecJson(JsonUtils.toJson(specification))
                .firstViolationStep(0)
                .statesJson(JsonUtils.toJson(List.of(state)))
                .inputEventsJson("[]")
                .seed(42L)
                .stateCount(2)
                .createdAt(LocalDateTime.now())
                .build();

        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toFindingSummaryDto(finding));

        finding.setStateCount(1);
        finding.setInputEventsJson("[{\"step\":0,\"kind\":\"DEVICE_VARIABLE\","
                + "\"targetId\":\"device-1\",\"property\":\"temperature\",\"value\":\"21\"}]");
        assertEquals("MODEL_CHOICE",
                mapper.toFindingDto(finding).getInputEvents().get(0).getSource());

        TraceStateDto trailingState = TraceStateDto.builder()
                .stateIndex(1)
                .devices(List.of())
                .triggeredRules(List.of())
                .compromisedAutomationLinks(List.of())
                .build();
        finding.setStatesJson(JsonUtils.toJson(List.of(state, trailingState)));
        finding.setStateCount(2);
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toFindingDto(finding));
        finding.setStatesJson(JsonUtils.toJson(List.of(state)));
        finding.setStateCount(1);

        finding.setInputEventsJson(JsonUtils.toJson(List.of(FuzzInputEventDto.builder()
                .step(0)
                .kind("DEVICE_STATE")
                .targetId("device-1")
                .property("state")
                .value("on")
                .source("SEED_EVENT")
                .build())));
        assertEquals("SEED_EVENT",
                mapper.toFindingDto(finding).getInputEvents().get(0).getSource());

        finding.setInputEventsJson(JsonUtils.toJson(List.of(FuzzInputEventDto.builder()
                .step(0)
                .kind("ENVIRONMENT_RATE")
                .targetId("environment")
                .property("temperature")
                .value("rate:1")
                .source("UNKNOWN_SOURCE")
                .build())));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toFindingDto(finding));

        finding.setFirstViolationStep(1);
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toFindingSummaryDto(finding));

        finding.setFirstViolationStep(0);
        finding.setInputEventsJson(JsonUtils.toJson(List.of(FuzzInputEventDto.builder()
                .step(1)
                .kind("DEVICE_VARIABLE")
                .build())));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toFindingSummaryDto(finding));

        finding.setInputEventsJson(JsonUtils.toJson(List.of(FuzzInputEventDto.builder()
                .step(0)
                .kind("UNSUPPORTED_KIND")
                .targetId("device-1")
                .property("temperature")
                .value("21")
                .build())));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toFindingSummaryDto(finding));
    }

    @Test
    void findingRejectsInputEventsOutsideCausalOrder() {
        SpecificationDto specification = supportedSpecification("spec-1");
        TraceStateDto first = TraceStateDto.builder()
                .stateIndex(0)
                .devices(List.of())
                .triggeredRules(List.of())
                .compromisedAutomationLinks(List.of())
                .build();
        TraceStateDto second = TraceStateDto.builder()
                .stateIndex(1)
                .devices(List.of())
                .triggeredRules(List.of())
                .compromisedAutomationLinks(List.of())
                .build();
        FuzzFindingPo finding = FuzzFindingPo.builder()
                .id(11L)
                .violatedSpecId("spec-1")
                .violatedSpecJson(JsonUtils.toJson(specification))
                .firstViolationStep(1)
                .statesJson(JsonUtils.toJson(List.of(first, second)))
                .seed(42L)
                .stateCount(2)
                .createdAt(LocalDateTime.now())
                .build();

        finding.setInputEventsJson(JsonUtils.toJson(List.of(
                inputEvent(0, "RANDOM_INITIAL_STATE"),
                inputEvent(0, "SEED_EVENT"),
                inputEvent(0, "MODEL_CHOICE"),
                inputEvent(1, "SEED_EVENT"),
                inputEvent(1, "MODEL_CHOICE"))));
        assertDoesNotThrow(() -> mapper.toFindingDto(finding));

        finding.setInputEventsJson(JsonUtils.toJson(List.of(
                inputEvent(1, "MODEL_CHOICE"), inputEvent(0, "MODEL_CHOICE"))));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toFindingDto(finding));

        finding.setInputEventsJson(JsonUtils.toJson(List.of(
                inputEvent(0, "MODEL_CHOICE"), inputEvent(0, "SEED_EVENT"))));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toFindingDto(finding));

        finding.setInputEventsJson(JsonUtils.toJson(List.of(
                inputEvent(1, "RANDOM_INITIAL_STATE"))));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toFindingDto(finding));
    }

    @Test
    void persistedRunRejectsInconsistentExecutionStatistics() {
        SpecificationDto specification = supportedSpecification("spec-1");
        FuzzTaskPo run = completedRun(
                List.of(specification),
                List.of("spec-1"),
                FuzzEligibilityDto.builder()
                        .eligibleSpecIds(List.of("spec-1"))
                        .requestedSpecCount(1)
                        .eligibleSpecCount(1)
                        .build(),
                FuzzOutcome.BUDGET_EXHAUSTED,
                0);

        run.setIterations(0);
        run.setGeneratedPaths(1L);
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));
        run.setIterations(1);
        run.setGeneratedPaths(0L);
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));
        run.setIterations(2);
        run.setGeneratedPaths(1L);
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));
        run.setGeneratedPaths(3L);
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));
        run.setPopulationSize(2);
        run.setGeneratedPaths(4L);
        assertDoesNotThrow(() -> mapper.toRunSummaryDto(run, List.of()));
        run.setMaxIterations(1);
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));
    }

    @Test
    void projectedRunRejectsInconsistentExecutionStatistics() {
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDtoFromTaskProjection(
                        projectedRun(0, 1L, 1, 10), List.of()));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDtoFromTaskProjection(
                        projectedRun(1, 0L, 1, 10), List.of()));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDtoFromTaskProjection(
                        projectedRun(2, 1L, 1, 10), List.of()));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDtoFromTaskProjection(
                        projectedRun(2, 3L, 1, 10), List.of()));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDtoFromTaskProjection(
                        projectedRun(2, 2L, 2, 1), List.of()));
        assertDoesNotThrow(() -> mapper.toRunSummaryDtoFromTaskProjection(
                projectedRun(2, 4L, 2, 10), List.of()));
    }

    @Test
    void runSummaryRejectsOutcomeAndFindingCountContradictions() {
        FuzzTaskPo run = FuzzTaskPo.builder()
                .id(7L)
                .status(FuzzTaskPo.TaskStatus.COMPLETED)
                .outcome(FuzzOutcome.BUDGET_EXHAUSTED)
                .findingCount(1)
                .build();
        FuzzFindingPo finding = FuzzFindingPo.builder().id(9L).build();

        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of(finding)));

        run.setFindingCount(0);
        run.setOutcome(FuzzOutcome.FOUND_VIOLATION);
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));

        run.setUserId(3L);
        run.setFindingCount(1);
        FuzzFindingPo crossUserFinding = FuzzFindingPo.builder()
                .id(10L)
                .userId(4L)
                .fuzzTaskId(7L)
                .violatedSpecId("spec-1")
                .build();
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of(crossUserFinding)));
    }

    @Test
    void runSummaryRejectsMissingRequiredScalarsAndEligibilityCountDrift() {
        LocalDateTime createdAt = LocalDateTime.of(2026, 7, 14, 12, 0);
        FuzzTaskPo run = FuzzTaskPo.builder()
                .id(12L)
                .userId(3L)
                .status(FuzzTaskPo.TaskStatus.COMPLETED)
                .createdAt(createdAt)
                .completedAt(createdAt.plusSeconds(1))
                .outcome(FuzzOutcome.BUDGET_EXHAUSTED)
                .iterations(1)
                .generatedPaths(1L)
                .elapsedMs(1L)
                .maxIterations(10)
                .pathLength(2)
                .populationSize(1)
                .findingCount(0)
                .targetSpecIdsJson("[]")
                .modelInputSnapshotJson(JsonUtils.toJson(inputSnapshot(List.of(
                        supportedSpecification("spec-1")))))
                .modelSnapshotJson(JsonUtils.toJson(ModelRunSnapshotDto.captured(
                        createdAt, 0, 0, 1, 0, 0)))
                .eligibilityJson(JsonUtils.toJson(FuzzEligibilityDto.builder()
                        .eligibleSpecIds(List.of("spec-1"))
                        .requestedSpecCount(1)
                        .eligibleSpecCount(1)
                        .build()))
                .limitationsJson("[]")
                .build();

        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));

        run.setEffectiveSeed(42L);
        run.setEligibilityJson(JsonUtils.toJson(FuzzEligibilityDto.builder()
                .eligibleSpecIds(List.of("spec-1"))
                .requestedSpecCount(2)
                .eligibleSpecCount(1)
                .build()));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));
    }

    @Test
    void runSummaryRejectsUnsupportedEligibleTemplate() {
        SpecificationDto unsupported = supportedSpecification("spec-1");
        unsupported.setTemplateId("6");
        FuzzTaskPo run = completedRun(
                List.of(unsupported),
                List.of("spec-1"),
                FuzzEligibilityDto.builder()
                        .eligibleSpecIds(List.of("spec-1"))
                        .requestedSpecCount(1)
                        .eligibleSpecCount(1)
                        .build(),
                FuzzOutcome.BUDGET_EXHAUSTED,
                0);

        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));
    }

    @Test
    void runSummaryRejectsTargetsAndFindingsOutsideFrozenSpecifications() {
        SpecificationDto frozen = supportedSpecification("spec-1");
        FuzzTaskPo unknownTargetRun = completedRun(
                List.of(frozen),
                List.of("spec-2"),
                FuzzEligibilityDto.builder()
                        .eligibleSpecIds(List.of("spec-2"))
                        .requestedSpecCount(1)
                        .eligibleSpecCount(1)
                        .build(),
                FuzzOutcome.BUDGET_EXHAUSTED,
                0);
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(unknownTargetRun, List.of()));

        FuzzTaskPo findingRun = completedRun(
                List.of(frozen),
                List.of("spec-1"),
                FuzzEligibilityDto.builder()
                        .eligibleSpecIds(List.of("spec-1"))
                        .requestedSpecCount(1)
                        .eligibleSpecCount(1)
                        .build(),
                FuzzOutcome.FOUND_VIOLATION,
                1);
        SpecificationDto alteredSnapshot = supportedSpecification("spec-1");
        alteredSnapshot.setTemplateLabel("altered persisted specification");
        FuzzFindingPo finding = finding(findingRun, alteredSnapshot);

        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(findingRun, List.of(finding)));
    }

    @Test
    void singleFindingDetailStillValidatesItsFrozenRunContext() {
        SpecificationDto specification = supportedSpecification("spec-1");
        FuzzTaskPo run = completedRun(
                List.of(specification),
                List.of("spec-1"),
                FuzzEligibilityDto.builder()
                        .eligibleSpecIds(List.of("spec-1"))
                        .requestedSpecCount(1)
                        .eligibleSpecCount(1)
                        .build(),
                FuzzOutcome.FOUND_VIOLATION,
                1);
        FuzzFindingPo finding = finding(run, specification);

        assertEquals(finding.getId(), mapper.toFindingDto(run, finding).getId());

        finding.setSeed(43L);
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toFindingDto(run, finding));
    }

    @Test
    void singleFindingDetailRejectsStateCountBeyondRunPathLength() {
        SpecificationDto specification = supportedSpecification("spec-1");
        FuzzTaskPo run = completedRun(
                List.of(specification),
                List.of("spec-1"),
                FuzzEligibilityDto.builder()
                        .eligibleSpecIds(List.of("spec-1"))
                        .requestedSpecCount(1)
                        .eligibleSpecCount(1)
                        .build(),
                FuzzOutcome.FOUND_VIOLATION,
                1);
        run.setPathLength(1);
        FuzzFindingPo finding = finding(run, specification);
        TraceStateDto first = TraceStateDto.builder()
                .stateIndex(0)
                .devices(List.of())
                .triggeredRules(List.of())
                .compromisedAutomationLinks(List.of())
                .build();
        TraceStateDto second = TraceStateDto.builder()
                .stateIndex(1)
                .devices(List.of())
                .triggeredRules(List.of())
                .compromisedAutomationLinks(List.of())
                .build();
        finding.setStatesJson(JsonUtils.toJson(List.of(first, second)));
        finding.setStateCount(2);
        finding.setFirstViolationStep(1);

        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toFindingDto(run, finding));
    }

    @Test
    void runSummaryRejectsEligibilityThatDoesNotPartitionFrozenTargets() {
        SpecificationDto first = supportedSpecification("spec-1");
        SpecificationDto second = supportedSpecification("spec-2");
        FuzzTaskPo run = completedRun(
                List.of(first, second),
                List.of(),
                FuzzEligibilityDto.builder()
                        .eligibleSpecIds(List.of("spec-1"))
                        .requestedSpecCount(1)
                        .eligibleSpecCount(1)
                        .build(),
                FuzzOutcome.BUDGET_EXHAUSTED,
                0);

        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));
    }

    @Test
    void runSummaryRejectsMissingSemanticLimitationDisclosure() {
        SpecificationDto specification = supportedSpecification("spec-1");
        FuzzTaskPo run = completedRun(
                List.of(specification),
                List.of("spec-1"),
                FuzzEligibilityDto.builder()
                        .eligibleSpecIds(List.of("spec-1"))
                        .requestedSpecCount(1)
                        .eligibleSpecCount(1)
                        .build(),
                FuzzOutcome.BUDGET_EXHAUSTED,
                0);
        run.setLimitationsJson(JsonUtils.toJson(List.of(
                "FINITE_TRACE_TEMPLATES_1_3_4_ONLY",
                "ATTACK_TRUST_PRIVACY_CONTENT_UNSUPPORTED")));

        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));
    }

    @Test
    void runSummaryRejectsUnboundedDiagnosticsAndLimitationCount() {
        SpecificationDto specification = supportedSpecification("spec-1");
        FuzzEligibilityDto eligibility = FuzzEligibilityDto.builder()
                .eligibleSpecIds(List.of())
                .eligibleSpecLabels(Map.of())
                .ineligibleSpecs(List.of(FuzzIneligibleSpecDto.builder()
                        .specId("spec-1")
                        .specificationLabel("spec-1")
                        .reasonCode("MODEL_INVALID")
                        .reason("x".repeat(501))
                        .build()))
                .requestedSpecCount(1)
                .eligibleSpecCount(0)
                .build();
        FuzzTaskPo run = completedRun(
                List.of(specification),
                List.of("spec-1"),
                eligibility,
                FuzzOutcome.INCONCLUSIVE,
                0);

        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));

        eligibility.getIneligibleSpecs().get(0).setReason("Model is invalid");
        run.setEligibilityJson(JsonUtils.toJson(eligibility));
        List<String> limitations = new java.util.ArrayList<>(FuzzLimitationContract.baseCodes());
        for (int index = limitations.size(); index <= 32; index++) {
            limitations.add("FUTURE_LIMITATION_" + index);
        }
        run.setLimitationsJson(JsonUtils.toJson(limitations));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(run, List.of()));
    }

    @Test
    void projectedImplicitAllEligibilityMustMatchFrozenSpecificationCount() {
        LocalDateTime createdAt = LocalDateTime.of(2026, 7, 15, 10, 0);
        FuzzTaskSummaryProjection run = mock(FuzzTaskSummaryProjection.class);
        when(run.getId()).thenReturn(88L);
        when(run.getUserId()).thenReturn(3L);
        when(run.getStatus()).thenReturn(FuzzTaskPo.TaskStatus.COMPLETED);
        when(run.getCreatedAt()).thenReturn(createdAt);
        when(run.getCompletedAt()).thenReturn(createdAt.plusSeconds(1));
        when(run.getOutcome()).thenReturn(FuzzOutcome.BUDGET_EXHAUSTED);
        when(run.getEffectiveSeed()).thenReturn(42L);
        when(run.getIterations()).thenReturn(1);
        when(run.getGeneratedPaths()).thenReturn(1L);
        when(run.getElapsedMs()).thenReturn(1L);
        when(run.getMaxIterations()).thenReturn(10);
        when(run.getPathLength()).thenReturn(2);
        when(run.getPopulationSize()).thenReturn(1);
        when(run.getFindingCount()).thenReturn(0);
        when(run.getExplorationMode()).thenReturn(FuzzExplorationMode.BOARD_SNAPSHOT);
        when(run.getTargetSpecIdsJson()).thenReturn("[]");
        when(run.getModelSnapshotJson()).thenReturn(JsonUtils.toJson(
                ModelRunSnapshotDto.captured(createdAt, 0, 0, 2, 0, 0)));
        when(run.getEligibilityJson()).thenReturn(JsonUtils.toJson(FuzzEligibilityDto.builder()
                .eligibleSpecIds(List.of("spec-1"))
                .eligibleSpecLabels(Map.of("spec-1", "Safety property"))
                .ineligibleSpecs(List.of())
                .requestedSpecCount(1)
                .eligibleSpecCount(1)
                .build()));
        when(run.getLimitationsJson()).thenReturn(
                JsonUtils.toJson(FuzzLimitationContract.baseCodes()));

        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDtoFromTaskProjection(run, List.of()));

        when(run.getModelSnapshotJson()).thenReturn(JsonUtils.toJson(
                ModelRunSnapshotDto.captured(createdAt, 0, 0, 1, 0, 0)));
        when(run.getEligibilityJson()).thenReturn(JsonUtils.toJson(FuzzEligibilityDto.builder()
                .eligibleSpecIds(List.of("spec-1"))
                .eligibleSpecLabels(Map.of("spec-1", "Safety\nproperty"))
                .ineligibleSpecs(List.of())
                .requestedSpecCount(1)
                .eligibleSpecCount(1)
                .build()));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDtoFromTaskProjection(run, List.of()));
    }

    @Test
    void projectedRunRejectsFindingStateCountBeyondRunPathLength() {
        LocalDateTime createdAt = LocalDateTime.of(2026, 7, 15, 11, 0);
        FuzzTaskSummaryProjection run = mock(FuzzTaskSummaryProjection.class);
        when(run.getId()).thenReturn(89L);
        when(run.getUserId()).thenReturn(3L);
        when(run.getStatus()).thenReturn(FuzzTaskPo.TaskStatus.COMPLETED);
        when(run.getCreatedAt()).thenReturn(createdAt);
        when(run.getCompletedAt()).thenReturn(createdAt.plusSeconds(1));
        when(run.getOutcome()).thenReturn(FuzzOutcome.FOUND_VIOLATION);
        when(run.getEffectiveSeed()).thenReturn(42L);
        when(run.getIterations()).thenReturn(1);
        when(run.getGeneratedPaths()).thenReturn(1L);
        when(run.getElapsedMs()).thenReturn(1L);
        when(run.getMaxIterations()).thenReturn(10);
        when(run.getPathLength()).thenReturn(1);
        when(run.getPopulationSize()).thenReturn(1);
        when(run.getFindingCount()).thenReturn(1);
        when(run.getExplorationMode()).thenReturn(FuzzExplorationMode.BOARD_SNAPSHOT);
        when(run.getTargetSpecIdsJson()).thenReturn(JsonUtils.toJson(List.of("spec-1")));
        when(run.getModelSnapshotJson()).thenReturn(JsonUtils.toJson(
                ModelRunSnapshotDto.captured(createdAt, 0, 0, 1, 0, 0)));
        when(run.getEligibilityJson()).thenReturn(JsonUtils.toJson(FuzzEligibilityDto.builder()
                .eligibleSpecIds(List.of("spec-1"))
                .eligibleSpecLabels(Map.of("spec-1", "Safety property"))
                .ineligibleSpecs(List.of())
                .requestedSpecCount(1)
                .eligibleSpecCount(1)
                .build()));
        when(run.getLimitationsJson()).thenReturn(
                JsonUtils.toJson(FuzzLimitationContract.baseCodes()));

        FuzzFindingSummaryProjection finding = mock(FuzzFindingSummaryProjection.class);
        when(finding.getId()).thenReturn(31L);
        when(finding.getUserId()).thenReturn(3L);
        when(finding.getFuzzTaskId()).thenReturn(89L);
        when(finding.getViolatedSpecId()).thenReturn("spec-1");
        when(finding.getFirstViolationStep()).thenReturn(1);
        when(finding.getSeed()).thenReturn(42L);
        when(finding.getStateCount()).thenReturn(2);
        when(finding.getCreatedAt()).thenReturn(createdAt.plusNanos(1));

        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDtoFromTaskProjection(run, List.of(finding)));
    }

    @Test
    void missingModeIsRejectedInsteadOfBeingRelabeledAsBoardSnapshot() {
        SpecificationDto specification = supportedSpecification("spec-1");
        FuzzTaskPo legacyRun = completedRun(
                List.of(specification),
                List.of("spec-1"),
                FuzzEligibilityDto.builder()
                        .eligibleSpecIds(List.of("spec-1"))
                        .requestedSpecCount(1)
                        .eligibleSpecCount(1)
                        .build(),
                FuzzOutcome.BUDGET_EXHAUSTED,
                0);
        legacyRun.setExplorationMode(null);

        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toTaskDto(legacyRun));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toTaskSummaryDto(legacyRun));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunDto(legacyRun, List.of()));
        assertThrows(PersistedDataIntegrityException.class,
                () -> mapper.toRunSummaryDto(legacyRun, List.of()));
    }

    private FuzzTaskSummaryProjection projectedRun(
            int iterations, long generatedPaths, int populationSize, int maxIterations) {
        LocalDateTime createdAt = LocalDateTime.of(2026, 7, 15, 12, 0);
        FuzzTaskSummaryProjection run = mock(FuzzTaskSummaryProjection.class);
        when(run.getId()).thenReturn(90L);
        when(run.getUserId()).thenReturn(3L);
        when(run.getStatus()).thenReturn(FuzzTaskPo.TaskStatus.COMPLETED);
        when(run.getCreatedAt()).thenReturn(createdAt);
        when(run.getCompletedAt()).thenReturn(createdAt.plusSeconds(1));
        when(run.getOutcome()).thenReturn(FuzzOutcome.BUDGET_EXHAUSTED);
        when(run.getExplorationMode()).thenReturn(FuzzExplorationMode.BOARD_SNAPSHOT);
        when(run.getEffectiveSeed()).thenReturn(42L);
        when(run.getIterations()).thenReturn(iterations);
        when(run.getGeneratedPaths()).thenReturn(generatedPaths);
        when(run.getElapsedMs()).thenReturn(1L);
        when(run.getMaxIterations()).thenReturn(maxIterations);
        when(run.getPathLength()).thenReturn(2);
        when(run.getPopulationSize()).thenReturn(populationSize);
        when(run.getFindingCount()).thenReturn(0);
        when(run.getTargetSpecIdsJson()).thenReturn("[]");
        when(run.getModelSnapshotJson()).thenReturn(JsonUtils.toJson(
                ModelRunSnapshotDto.captured(createdAt, 0, 0, 1, 0, 0)));
        when(run.getEligibilityJson()).thenReturn(JsonUtils.toJson(FuzzEligibilityDto.builder()
                .eligibleSpecIds(List.of("spec-1"))
                .eligibleSpecLabels(Map.of("spec-1", "Safety property"))
                .ineligibleSpecs(List.of())
                .requestedSpecCount(1)
                .eligibleSpecCount(1)
                .build()));
        when(run.getLimitationsJson()).thenReturn(
                JsonUtils.toJson(FuzzLimitationContract.baseCodes()));
        return run;
    }

    private FuzzInputEventDto inputEvent(int step, String source) {
        return FuzzInputEventDto.builder()
                .step(step)
                .kind("DEVICE_VARIABLE")
                .targetId("device-1")
                .property("temperature")
                .value("21")
                .source(source)
                .build();
    }

    private FuzzTaskPo completedRun(
            List<SpecificationDto> specifications,
            List<String> targetSpecIds,
            FuzzEligibilityDto eligibility,
            FuzzOutcome outcome,
            int findingCount) {
        LocalDateTime createdAt = LocalDateTime.of(2026, 7, 14, 15, 0);
        if (eligibility.getEligibleSpecLabels() == null
                || eligibility.getEligibleSpecLabels().isEmpty()) {
            Map<String, SpecificationDto> byId = specifications.stream()
                    .collect(java.util.stream.Collectors.toMap(
                            SpecificationDto::getId, specification -> specification));
            Map<String, String> labels = new java.util.LinkedHashMap<>();
            for (String id : eligibility.getEligibleSpecIds()) {
                SpecificationDto specification = byId.get(id);
                labels.put(id, specification != null && specification.getTemplateLabel() != null
                        ? specification.getTemplateLabel() : id);
            }
            eligibility.setEligibleSpecLabels(labels);
        }
        return FuzzTaskPo.builder()
                .id(20L)
                .userId(3L)
                .status(FuzzTaskPo.TaskStatus.COMPLETED)
                .createdAt(createdAt)
                .completedAt(createdAt.plusSeconds(2))
                .progress(100)
                .targetSpecIdsJson(JsonUtils.toJson(targetSpecIds))
                .maxIterations(10)
                .pathLength(2)
                .populationSize(1)
                .explorationMode(FuzzExplorationMode.BOARD_SNAPSHOT)
                .modelInputSnapshotJson(JsonUtils.toJson(inputSnapshot(specifications)))
                .modelSnapshotJson(JsonUtils.toJson(ModelRunSnapshotDto.captured(
                        createdAt, 0, 0, specifications.size(), 0, 0)))
                .outcome(outcome)
                .effectiveSeed(42L)
                .iterations(1)
                .generatedPaths(1L)
                .elapsedMs(1L)
                .eligibilityJson(JsonUtils.toJson(eligibility))
                .limitationsJson(JsonUtils.toJson(FuzzLimitationContract.baseCodes()))
                .findingCount(findingCount)
                .build();
    }

    private FuzzFindingPo finding(FuzzTaskPo run, SpecificationDto specification) {
        TraceStateDto state = TraceStateDto.builder()
                .stateIndex(0)
                .devices(List.of())
                .triggeredRules(List.of())
                .compromisedAutomationLinks(List.of())
                .build();
        return FuzzFindingPo.builder()
                .id(30L)
                .userId(run.getUserId())
                .fuzzTaskId(run.getId())
                .violatedSpecId(specification.getId())
                .violatedSpecJson(JsonUtils.toJson(specification))
                .firstViolationStep(0)
                .statesJson(JsonUtils.toJson(List.of(state)))
                .inputEventsJson("[]")
                .seed(run.getEffectiveSeed())
                .stateCount(1)
                .createdAt(run.getCreatedAt().plusSeconds(1))
                .build();
    }

    private ModelInputSnapshot inputSnapshot(List<SpecificationDto> specifications) {
        return new ModelInputSnapshot(
                List.of(), List.of(), List.of(), List.of(), specifications, Map.of());
    }

    private SpecificationDto supportedSpecification(String id) {
        SpecConditionDto condition = new SpecConditionDto();
        condition.setId(id + "-condition");
        condition.setSide("a");
        condition.setDeviceId("device-1");
        condition.setTargetType("state");
        condition.setKey("state");
        condition.setRelation("=");
        condition.setValue("on");
        SpecificationDto specification = new SpecificationDto();
        specification.setId(id);
        specification.setTemplateId("1");
        specification.setAConditions(List.of(condition));
        return specification;
    }
}
