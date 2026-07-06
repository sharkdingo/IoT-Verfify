package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerationContext;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;

import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.verification.SpecResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRequestDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.po.VerificationTaskPo;
import cn.edu.nju.Iot_Verify.repository.TraceRepository;
import cn.edu.nju.Iot_Verify.repository.VerificationTaskRepository;
import cn.edu.nju.Iot_Verify.util.mapper.SpecificationMapper;
import cn.edu.nju.Iot_Verify.util.mapper.TraceMapper;
import cn.edu.nju.Iot_Verify.util.mapper.VerificationTaskMapper;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.springframework.scheduling.concurrent.ThreadPoolTaskExecutor;
import org.springframework.core.task.TaskRejectedException;

import java.util.Map;
import org.mockito.junit.jupiter.MockitoExtension;


import java.lang.reflect.Method;
import java.io.File;
import java.lang.reflect.Field;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.LocalDateTime;
import java.util.*;
import java.util.concurrent.Future;
import java.util.concurrent.ThreadPoolExecutor;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

/**
 * Tests for VerificationServiceImpl.buildVerificationResult fail-closed logic.
 * Uses reflection to invoke the private method directly.
 */
@ExtendWith(MockitoExtension.class)
class VerificationServiceImplBuildResultTest {

    @Mock private SmvGenerator smvGenerator;
    @Mock private SmvTraceParser smvTraceParser;
    @Mock private NusmvExecutor nusmvExecutor;
    @Mock private NusmvConfig nusmvConfig;
    @Mock private VerificationTaskRepository taskRepository;
    @Mock private TraceRepository traceRepository;
    @Mock private TraceMapper traceMapper;
    @Mock private SpecificationMapper specificationMapper;
    @Mock private VerificationTaskMapper verificationTaskMapper;

    private static class DirectThreadPoolTaskExecutor extends ThreadPoolTaskExecutor {
        @Override
        public void execute(Runnable task) {
            task.run();
        }

        @Override
        public void execute(Runnable task, long startTimeout) {
            task.run();
        }
    }

    private static class RejectingThreadPoolTaskExecutor extends ThreadPoolTaskExecutor {
        @Override
        public void execute(Runnable task) {
            throw new TaskRejectedException("rejected");
        }

        @Override
        public void execute(Runnable task, long startTimeout) {
            throw new TaskRejectedException("rejected");
        }
    }

    private static class CapturingThreadPoolTaskExecutor extends ThreadPoolTaskExecutor {
        private Runnable capturedTask;

        @Override
        public void execute(Runnable task) {
            capturedTask = task;
        }

        @Override
        public void execute(Runnable task, long startTimeout) {
            capturedTask = task;
        }

        Runnable capturedTask() {
            return capturedTask;
        }
    }

    private VerificationServiceImpl service;
    private ThreadPoolTaskExecutor verificationTaskExecutor;
    private ThreadPoolTaskExecutor syncVerificationExecutor;
    private Method buildVerificationResult;

    @BeforeEach
    void setUp() throws Exception {
        verificationTaskExecutor = new DirectThreadPoolTaskExecutor();
        syncVerificationExecutor = new ThreadPoolTaskExecutor();
        syncVerificationExecutor.setCorePoolSize(1);
        syncVerificationExecutor.setMaxPoolSize(1);
        syncVerificationExecutor.setQueueCapacity(10);
        syncVerificationExecutor.setThreadNamePrefix("test-sync-verify-");
        syncVerificationExecutor.initialize();

        service = new VerificationServiceImpl(
                smvGenerator, smvTraceParser, nusmvExecutor, nusmvConfig,
                taskRepository, traceRepository, traceMapper,
                specificationMapper, verificationTaskMapper, new ObjectMapper(),
                verificationTaskExecutor, syncVerificationExecutor, null);

        buildVerificationResult = VerificationServiceImpl.class.getDeclaredMethod(
                "buildVerificationResult",
                NusmvResult.class, List.class, List.class, List.class,
                Long.class, Long.class, List.class, Map.class, String.class,
                List.class, int.class, int.class);
        buildVerificationResult.setAccessible(true);
    }

    private VerificationServiceImpl serviceWithVerificationExecutor(ThreadPoolTaskExecutor executor) {
        return new VerificationServiceImpl(
                smvGenerator, smvTraceParser, nusmvExecutor, nusmvConfig,
                taskRepository, traceRepository, traceMapper,
                specificationMapper, verificationTaskMapper, new ObjectMapper(),
                executor, syncVerificationExecutor, null);
    }

    @AfterEach
    void tearDown() {
        syncVerificationExecutor.shutdown();
    }

    private VerificationResultDto invoke(NusmvResult result,
                                         List<DeviceVerificationDto> devices,
                                         List<SpecificationDto> specs,
                                         List<String> checkLogs) throws Exception {
        return (VerificationResultDto) buildVerificationResult.invoke(
                service, result, devices, List.of(), specs, 1L, null, checkLogs, Map.of(), null,
                emittedSpecsFor(specs), 0, 0);
    }

    private VerificationResultDto invoke(NusmvResult result,
                                         List<DeviceVerificationDto> devices,
                                         List<SpecificationDto> specs,
                                         List<String> checkLogs,
                                         List<SmvGenerationContext.EmittedSpec> emittedSpecs) throws Exception {
        return (VerificationResultDto) buildVerificationResult.invoke(
                service, result, devices, List.of(), specs, 1L, null, checkLogs, Map.of(), null,
                emittedSpecs, 0, 0);
    }

    private List<SmvGenerationContext.EmittedSpec> emittedSpecsFor(List<SpecificationDto> specs) {
        if (specs == null) {
            return List.of();
        }
        return specs.stream()
                .filter(Objects::nonNull)
                .filter(s -> (s.getAConditions() != null && !s.getAConditions().isEmpty()) ||
                             (s.getIfConditions() != null && !s.getIfConditions().isEmpty()))
                .map(s -> new SmvGenerationContext.EmittedSpec(s, s.getId(), ""))
                .toList();
    }

    private SmvGenerator.GenerateResult generateResult(File smvFile, List<SpecificationDto> emittedSpecs) {
        return new SmvGenerator.GenerateResult(smvFile, Map.of(), List.of(), 0, 0, emittedSpecsFor(emittedSpecs));
    }

    private List<DeviceVerificationDto> singleDevice() {
        DeviceVerificationDto d = new DeviceVerificationDto();
        d.setVarName("testDevice");
        d.setTemplateName("light");
        return List.of(d);
    }

    private File createTempModelFile() throws Exception {
        Path dir = Files.createTempDirectory("verify-service-test-");
        File smvFile = dir.resolve("model.smv").toFile();
        assertTrue(smvFile.createNewFile());
        smvFile.deleteOnExit();
        dir.toFile().deleteOnExit();
        return smvFile;
    }

    private int readResultCode(File smvFile) throws Exception {
        File jsonFile = new File(smvFile.getParentFile(), "result.json");
        assertTrue(jsonFile.exists());
        JsonNode node = new ObjectMapper().readTree(jsonFile);
        return node.path("code").asInt();
    }

    private JsonNode readRequestJson(File smvFile) throws Exception {
        File jsonFile = new File(smvFile.getParentFile(), "request.json");
        assertTrue(jsonFile.exists());
        return new ObjectMapper().readTree(jsonFile);
    }

    @SuppressWarnings("unchecked")
    private Set<Long> cancelledTaskIds() throws Exception {
        Field f = AbstractAsyncTaskService.class.getDeclaredField("cancelledTasks");
        f.setAccessible(true);
        return (Set<Long>) f.get(service);
    }

    // --- effectiveSpecs = 0: all specs filtered out -> unsafe/unreliable ---

    @Test
    void effectiveSpecsEmpty_returnsUnsafeBecauseNothingWasVerified() throws Exception {
        // Spec with no A/IF conditions -> filtered out
        SpecificationDto emptySpec = new SpecificationDto();
        emptySpec.setId("s1");
        emptySpec.setAConditions(List.of());
        emptySpec.setIfConditions(List.of());

        NusmvResult result = NusmvResult.success("", List.of());
        List<String> logs = new ArrayList<>();

        VerificationResultDto dto = invoke(result, List.of(), List.of(emptySpec), logs);

        assertFalse(dto.isSafe());
        assertTrue(dto.getSpecResults().isEmpty());
        assertTrue(logs.stream().anyMatch(l -> l.contains("No valid specifications")));
        assertTrue(logs.stream().anyMatch(l -> l.contains("no specifications were emitted")));
    }

    // --- specCheckResults empty but effectiveSpecs > 0 -> fail-closed ---

    @Test
    void emptySpecResults_withEffectiveSpecs_failClosed() throws Exception {
        SpecificationDto spec = makeEffectiveSpec("s1");
        NusmvResult result = NusmvResult.success("some output", List.of());
        List<String> logs = new ArrayList<>();

        VerificationResultDto dto = invoke(result, List.of(), List.of(spec), logs);

        assertFalse(dto.isSafe());
        assertEquals(1, dto.getSpecResults().size());
        assertSpecResult(dto.getSpecResults().get(0), "s1", false, "");
        assertTrue(logs.stream().anyMatch(l -> l.contains("fail-closed")));
        assertTrue(logs.stream().anyMatch(l -> l.contains("incomplete/unreliable")));
    }

    // --- mismatch: fewer results than specs -> fail-closed, missing padded false ---

    @Test
    void fewerResultsThanSpecs_failClosedAndPadsFalse() throws Exception {
        SpecificationDto spec1 = makeEffectiveSpec("s1");
        SpecificationDto spec2 = makeEffectiveSpec("s2");

        // NuSMV only returned 1 result for 2 specs
        SpecCheckResult scr = new SpecCheckResult("expr1", true, null);
        NusmvResult result = NusmvResult.success("output", List.of(scr));

        List<String> logs = new ArrayList<>();

        VerificationResultDto dto = invoke(result, List.of(), List.of(spec1, spec2), logs);

        assertFalse(dto.isSafe());
        assertEquals(2, dto.getSpecResults().size());
        assertSpecResult(dto.getSpecResults().get(0), "s1", true, "expr1");
        assertSpecResult(dto.getSpecResults().get(1), "s2", false, "");
        assertTrue(logs.stream().anyMatch(l -> l.contains("mismatch")));
        assertTrue(logs.stream().anyMatch(l -> l.contains("missing")));
        assertTrue(logs.stream().anyMatch(l -> l.contains("incomplete/unreliable")));
    }

    // --- mismatch: more results than specs -> fail-closed, extras discarded ---

    @Test
    void moreResultsThanSpecs_failClosedAndTruncates() throws Exception {
        SpecificationDto spec1 = makeEffectiveSpec("s1");

        // NuSMV returned 2 results for 1 spec
        SpecCheckResult scr1 = new SpecCheckResult("expr1", true, null);
        SpecCheckResult scr2 = new SpecCheckResult("expr2", false, null);
        NusmvResult result = NusmvResult.success("output", List.of(scr1, scr2));

        List<String> logs = new ArrayList<>();

        VerificationResultDto dto = invoke(result, List.of(), List.of(spec1), logs);

        assertFalse(dto.isSafe());
        // specResults should be exactly effectiveSpecs.size() = 1, not 2
        assertEquals(1, dto.getSpecResults().size());
        assertTrue(logs.stream().anyMatch(l -> l.contains("extra")));
        assertTrue(logs.stream().anyMatch(l -> l.contains("incomplete/unreliable")));
    }

    // --- exact match, all pass -> safe=true ---

    @Test
    void exactMatch_allPass_safeTrue() throws Exception {
        SpecificationDto spec1 = makeEffectiveSpec("s1");
        SpecCheckResult scr = new SpecCheckResult("expr1", true, null);
        NusmvResult result = NusmvResult.success("output", List.of(scr));

        List<String> logs = new ArrayList<>();

        VerificationResultDto dto = invoke(result, List.of(), List.of(spec1), logs);

        assertTrue(dto.isSafe());
        assertEquals(1, dto.getSpecResults().size());
        assertSpecResult(dto.getSpecResults().get(0), "s1", true, "expr1");
    }

    @Test
    void exactMatch_usesRealEmittedSpecsForPlaceholderSpec() throws Exception {
        SpecificationDto specA = makeEffectiveSpec("a");
        SpecificationDto specB = makeEffectiveSpec("b");
        SpecificationDto specC = makeEffectiveSpec("c");
        List<SmvGenerationContext.EmittedSpec> emittedSpecs = List.of(
                new SmvGenerationContext.EmittedSpec(specA, "a", "CTLSPEC AG(a_ok)"),
                new SmvGenerationContext.EmittedSpec(specB, "b", "CTLSPEC FALSE"),
                new SmvGenerationContext.EmittedSpec(specC, "c", "CTLSPEC AG(c_ok)"));

        NusmvResult result = NusmvResult.success("output", List.of(
                new SpecCheckResult("CTLSPEC AG(a_ok)", true, null),
                new SpecCheckResult("", true, null),
                new SpecCheckResult("CTLSPEC AG(c_ok)", false, null)));
        List<String> logs = new ArrayList<>();

        VerificationResultDto dto = invoke(result, List.of(), List.of(specA, specB, specC), logs, emittedSpecs);

        assertFalse(dto.isSafe());
        assertEquals(3, dto.getSpecResults().size());
        assertSpecResult(dto.getSpecResults().get(0), "a", true, "CTLSPEC AG(a_ok)");
        assertSpecResult(dto.getSpecResults().get(1), "b", true, "CTLSPEC FALSE");
        assertSpecResult(dto.getSpecResults().get(2), "c", false, "CTLSPEC AG(c_ok)");
    }

    @Test
    void verify_executorRejected_throwsServiceUnavailable() {
        syncVerificationExecutor.shutdown();

        ServiceUnavailableException ex = assertThrows(ServiceUnavailableException.class,
                () -> service.verify(
                        1L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 0, false)));
        assertTrue(ex.getMessage().contains("busy"));
    }

    @Test
    void verify_nusmvBusy_throwsServiceUnavailable() throws Exception {
        when(nusmvConfig.getTimeoutMs()).thenReturn(1000L);
        File smv = createTempModelFile();
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any()))
                .thenReturn(generateResult(smv, List.of(makeEffectiveSpec("s1"))));
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(NusmvResult.busy("NuSMV execution is busy, please retry later"));

        ServiceUnavailableException ex = assertThrows(ServiceUnavailableException.class,
                () -> service.verify(
                        1L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 0, false)));
        assertTrue(ex.getMessage().contains("busy"));
        assertEquals(503, readResultCode(smv));
        JsonNode request = readRequestJson(smv);
        assertFalse(request.path("attack").asBoolean());
        assertEquals(0, request.path("intensity").asInt());
        assertEquals(1, request.path("specs").size());
    }

    @Test
    void verify_smvGenerationError_rethrowsSmvGenerationException() throws Exception {
        when(nusmvConfig.getTimeoutMs()).thenReturn(1000L);
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any()))
                .thenThrow(SmvGenerationException.ambiguousDeviceReference("Sensor", List.of("sensor_1", "sensor_2")));

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> service.verify(
                        1L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 0, false)));
        assertEquals("AMBIGUOUS_DEVICE_REFERENCE", ex.getErrorCategory());
    }

    @Test
    void submitVerification_emptySpecs_rejectsBeforeCreatingTask() {
        ValidationException ex = assertThrows(ValidationException.class,
                () -> service.submitVerification(
                        1L, makeRequest(singleDevice(), List.of(), List.of(), false, 0, false)));

        assertTrue(ex.getMessage().contains("Specs list cannot be empty"));
        verify(taskRepository, never()).save(any(VerificationTaskPo.class));
    }

    @Test
    void verifyAsync_emptySpecs_rejectsBeforeQueueingTask() {
        ValidationException ex = assertThrows(ValidationException.class,
                () -> service.verifyAsync(
                        1L, 7L, makeRequest(singleDevice(), List.of(), List.of(), false, 0, false)));

        assertTrue(ex.getMessage().contains("Specs list cannot be empty"));
        verify(taskRepository, never()).startTaskIfStillPending(
                anyLong(), any(), any(LocalDateTime.class), anyInt(), anyString(), any());
    }

    @Test
    void verifyAsync_nullTaskId_rejectsBeforeQueueingTask() throws Exception {
        ValidationException ex = assertThrows(ValidationException.class,
                () -> service.verifyAsync(
                        1L, null, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 0, false)));

        assertTrue(ex.getMessage().contains("taskId"));
        verify(taskRepository, never()).startTaskIfStillPending(
                anyLong(), any(), any(LocalDateTime.class), anyInt(), anyString(), any());
        verify(smvGenerator, never()).generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any());
    }

    @Test
    void submitVerification_invalidIntensity_rejectsBeforeCreatingTask() throws Exception {
        ValidationException ex = assertThrows(ValidationException.class,
                () -> service.submitVerification(
                        1L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 51, false)));

        assertTrue(ex.getMessage().contains("Intensity must be between 0 and 50"));
        verify(taskRepository, never()).save(any(VerificationTaskPo.class));
        verify(smvGenerator, never()).generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any());
    }

    @Test
    void verify_invalidIntensity_rejectsBeforeSubmittingSyncExecutor() throws Exception {
        ValidationException ex = assertThrows(ValidationException.class,
                () -> service.verify(
                        1L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, -1, false)));

        assertTrue(ex.getMessage().contains("Intensity must be between 0 and 50"));
        verify(smvGenerator, never()).generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any());
    }

    @Test
    void verifyAsync_invalidIntensity_marksExistingTaskFailedBeforeQueueing() throws Exception {
        VerificationTaskPo task = VerificationTaskPo.builder()
                .id(16L).userId(1L).status(VerificationTaskPo.TaskStatus.PENDING)
                .createdAt(LocalDateTime.now()).build();
        when(taskRepository.findById(16L)).thenReturn(Optional.of(task));

        ValidationException ex = assertThrows(ValidationException.class,
                () -> service.verifyAsync(
                        1L, 16L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 51, false)));

        assertTrue(ex.getMessage().contains("Intensity must be between 0 and 50"));
        verify(taskRepository).failTaskIfNotCancelled(
                eq(16L), eq(VerificationTaskPo.TaskStatus.FAILED), any(LocalDateTime.class),
                eq("intensity: Intensity must be between 0 and 50"), anyString(), any(),
                eq(VerificationTaskPo.TaskStatus.CANCELLED));
        verify(taskRepository, never()).startTaskIfStillPending(
                anyLong(), any(), any(LocalDateTime.class), anyInt(), anyString(), any());
        verify(smvGenerator, never()).generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any());
    }

    @Test
    void submitVerification_invalidNestedDevice_rejectsBeforeCreatingTask() throws Exception {
        DeviceVerificationDto invalidDevice = new DeviceVerificationDto();
        invalidDevice.setVarName(" ");
        invalidDevice.setTemplateName("light");

        ValidationException ex = assertThrows(ValidationException.class,
                () -> service.submitVerification(
                        1L, makeRequest(List.of(invalidDevice), List.of(), List.of(makeEffectiveSpec("s1")), false, 0, false)));

        assertTrue(ex.getMessage().contains("Device varName is required"));
        verify(taskRepository, never()).save(any(VerificationTaskPo.class));
        verify(smvGenerator, never()).generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any());
    }

    @Test
    void submitVerification_ruleWithNullCommand_rejectsBeforeCreatingTask() throws Exception {
        RuleDto invalidRule = makeRule();
        invalidRule.setCommand(null);

        ValidationException ex = assertThrows(ValidationException.class,
                () -> service.submitVerification(
                        1L, makeRequest(singleDevice(), List.of(invalidRule), List.of(makeEffectiveSpec("s1")), false, 0, false)));

        assertEquals("Command cannot be null", ex.getErrors().get("rules[0].command"));
        verify(taskRepository, never()).save(any(VerificationTaskPo.class));
        verify(smvGenerator, never()).generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any());
    }

    @Test
    void submitVerification_ruleWithBlankCommandFields_rejectsBeforeCreatingTask() throws Exception {
        RuleDto invalidRule = makeRule();
        invalidRule.setCommand(RuleDto.Command.builder()
                .deviceName(" ")
                .action("")
                .build());

        ValidationException ex = assertThrows(ValidationException.class,
                () -> service.submitVerification(
                        1L, makeRequest(singleDevice(), List.of(invalidRule), List.of(makeEffectiveSpec("s1")), false, 0, false)));

        assertEquals("Command device name is required", ex.getErrors().get("rules[0].command.deviceName"));
        assertEquals("Command action is required", ex.getErrors().get("rules[0].command.action"));
        verify(taskRepository, never()).save(any(VerificationTaskPo.class));
        verify(smvGenerator, never()).generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any());
    }

    @Test
    void submitVerification_invalidNestedSpec_rejectsBeforeCreatingTask() throws Exception {
        SpecificationDto invalidSpec = makeEffectiveSpec("s1");
        invalidSpec.setTemplateId("8");

        ValidationException ex = assertThrows(ValidationException.class,
                () -> service.submitVerification(
                        1L, makeRequest(singleDevice(), List.of(), List.of(invalidSpec), false, 0, false)));

        assertTrue(ex.getMessage().contains("Template ID must be one of"));
        verify(taskRepository, never()).save(any(VerificationTaskPo.class));
        verify(smvGenerator, never()).generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any());
    }

    @Test
    void submitVerification_nullSpecCondition_rejectsBeforeCreatingTask() throws Exception {
        SpecificationDto invalidSpec = makeEffectiveSpec("s1");
        invalidSpec.setAConditions(Collections.singletonList(null));

        ValidationException ex = assertThrows(ValidationException.class,
                () -> service.submitVerification(
                        1L, makeRequest(singleDevice(), List.of(), List.of(invalidSpec), false, 0, false)));

        assertTrue(ex.getMessage().contains("A-condition item cannot be null"));
        verify(taskRepository, never()).save(any(VerificationTaskPo.class));
        verify(smvGenerator, never()).generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any());
    }

    @Test
    void submitVerification_missingDisplayOnlyTemplateLabel_isAllowedByRuntimeValidation() throws Exception {
        CapturingThreadPoolTaskExecutor capturingExecutor = new CapturingThreadPoolTaskExecutor();
        VerificationServiceImpl capturingService = serviceWithVerificationExecutor(capturingExecutor);
        VerificationTaskPo savedTask = VerificationTaskPo.builder()
                .id(17L).userId(1L).status(VerificationTaskPo.TaskStatus.PENDING)
                .createdAt(LocalDateTime.now()).build();
        SpecificationDto spec = makeEffectiveSpec("s1");
        spec.setTemplateLabel(null);

        when(taskRepository.save(any(VerificationTaskPo.class))).thenReturn(savedTask);

        Long taskId = capturingService.submitVerification(
                1L, makeRequest(singleDevice(), List.of(), List.of(spec), false, 0, false));

        assertEquals(17L, taskId);
        assertNotNull(capturingExecutor.capturedTask());
        verify(taskRepository).save(any(VerificationTaskPo.class));
        verify(smvGenerator, never()).generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any());
    }

    @Test
    void submitVerification_queueRejected_marksCreatedTaskFailedAndThrowsServiceUnavailable() {
        VerificationServiceImpl rejectingService = serviceWithVerificationExecutor(new RejectingThreadPoolTaskExecutor());
        VerificationTaskPo savedTask = VerificationTaskPo.builder()
                .id(12L).userId(1L).status(VerificationTaskPo.TaskStatus.PENDING)
                .createdAt(LocalDateTime.now()).build();

        when(taskRepository.save(any(VerificationTaskPo.class))).thenReturn(savedTask);
        when(taskRepository.findById(12L)).thenReturn(Optional.of(savedTask));

        ServiceUnavailableException ex = assertThrows(ServiceUnavailableException.class,
                () -> rejectingService.submitVerification(
                        1L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 0, false)));

        assertTrue(ex.getMessage().contains("busy"));
        verify(taskRepository).save(any(VerificationTaskPo.class));
        verify(taskRepository).failTaskIfNotCancelled(
                eq(12L), eq(VerificationTaskPo.TaskStatus.FAILED), any(LocalDateTime.class),
                eq("Server busy, please try again later"), anyString(), any(),
                eq(VerificationTaskPo.TaskStatus.CANCELLED));
        verify(taskRepository, never()).startTaskIfStillPending(
                anyLong(), any(), any(LocalDateTime.class), anyInt(), anyString(), any());
    }

    @Test
    void verifyAsync_queueRejected_marksExistingTaskFailedAndThrowsServiceUnavailable() {
        VerificationServiceImpl rejectingService = serviceWithVerificationExecutor(new RejectingThreadPoolTaskExecutor());
        VerificationTaskPo task = VerificationTaskPo.builder()
                .id(13L).userId(1L).status(VerificationTaskPo.TaskStatus.PENDING)
                .createdAt(LocalDateTime.now()).build();

        when(taskRepository.findById(13L)).thenReturn(Optional.of(task));

        ServiceUnavailableException ex = assertThrows(ServiceUnavailableException.class,
                () -> rejectingService.verifyAsync(
                        1L, 13L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 0, false)));

        assertTrue(ex.getMessage().contains("busy"));
        verify(taskRepository).failTaskIfNotCancelled(
                eq(13L), eq(VerificationTaskPo.TaskStatus.FAILED), any(LocalDateTime.class),
                eq("Server busy, please try again later"), anyString(), any(),
                eq(VerificationTaskPo.TaskStatus.CANCELLED));
        verify(taskRepository, never()).startTaskIfStillPending(
                anyLong(), any(), any(LocalDateTime.class), anyInt(), anyString(), any());
    }

    @Test
    void verifyAsync_usesSubmissionTimeRequestSnapshot() throws Exception {
        CapturingThreadPoolTaskExecutor capturingExecutor = new CapturingThreadPoolTaskExecutor();
        VerificationServiceImpl capturingService = serviceWithVerificationExecutor(capturingExecutor);
        File smv = createTempModelFile();
        SpecificationDto spec = makeEffectiveSpec("s1");
        List<DeviceVerificationDto> devices = new ArrayList<>(singleDevice());
        RuleDto rule = makeRule();
        List<RuleDto> rules = new ArrayList<>(List.of(rule));
        List<SpecificationDto> specs = new ArrayList<>(List.of(spec));
        VerificationRequestDto request = makeRequest(devices, rules, specs, false, 0, false);

        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any()))
                .thenReturn(generateResult(smv, List.of(spec)));
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(NusmvResult.success("output", List.of(new SpecCheckResult("expr", true, null))));
        when(taskRepository.startTaskIfStillPending(anyLong(), any(), any(LocalDateTime.class), anyInt(), anyString(), any())).thenReturn(1);
        VerificationTaskPo task = VerificationTaskPo.builder()
                .id(14L).userId(1L).status(VerificationTaskPo.TaskStatus.RUNNING)
                .createdAt(LocalDateTime.now()).build();
        when(taskRepository.findById(14L)).thenReturn(Optional.of(task));

        capturingService.verifyAsync(1L, 14L, request);
        assertNotNull(capturingExecutor.capturedTask());

        devices.get(0).setVarName("mutatedDevice");
        rule.getConditions().get(0).setDeviceName("mutatedRuleDevice");
        spec.setId("mutatedSpec");
        spec.getAConditions().get(0).setValue("off");
        devices.clear();
        rules.clear();
        specs.clear();
        request.setSpecs(List.of(makeEffectiveSpec("mutated")));

        capturingExecutor.capturedTask().run();

        verify(smvGenerator).generate(eq(1L),
                argThat(sentDevices -> sentDevices.size() == 1
                        && "testDevice".equals(sentDevices.get(0).getVarName())),
                argThat(sentRules -> sentRules.size() == 1
                        && "sensor".equals(sentRules.get(0).getConditions().get(0).getDeviceName())),
                argThat(sentSpecs -> sentSpecs.size() == 1
                        && "s1".equals(sentSpecs.get(0).getId())
                        && "on".equals(sentSpecs.get(0).getAConditions().get(0).getValue())),
                eq(false), eq(0), eq(false), any());
        JsonNode requestJson = readRequestJson(smv);
        assertEquals("testDevice", requestJson.path("devices").get(0).path("varName").asText());
        assertEquals("sensor", requestJson.path("rules").get(0).path("conditions").get(0).path("deviceName").asText());
        assertEquals("s1", requestJson.path("specs").get(0).path("id").asText());
        assertEquals("on", requestJson.path("specs").get(0).path("aConditions").get(0).path("value").asText());
    }

    @Test
    void verifyAsync_success_writesResultJson() throws Exception {
        File smv = createTempModelFile();
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any()))
                .thenReturn(generateResult(smv, List.of(makeEffectiveSpec("s1"))));
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(NusmvResult.success("output", List.of(new SpecCheckResult("expr", true, null))));

        when(taskRepository.startTaskIfStillPending(anyLong(), any(), any(LocalDateTime.class), anyInt(), anyString(), any())).thenReturn(1);
        // findById is still used by verifyAsync after startTaskIfStillPending to load the entity
        VerificationTaskPo task = VerificationTaskPo.builder()
                .id(7L).userId(1L).status(VerificationTaskPo.TaskStatus.RUNNING)
                .createdAt(LocalDateTime.now()).build();
        when(taskRepository.findById(7L)).thenReturn(Optional.of(task));

        service.verifyAsync(
                1L, 7L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 0, false));

        assertEquals(200, readResultCode(smv));
        JsonNode request = readRequestJson(smv);
        assertFalse(request.path("attack").asBoolean());
        assertEquals(0, request.path("intensity").asInt());
        assertEquals(1, request.path("specs").size());
    }

    @Test
    void verifyAsync_failedSpecWithoutTrace_countsViolatedSpecFromSpecResults() throws Exception {
        File smv = createTempModelFile();
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any()))
                .thenReturn(generateResult(smv, List.of(makeEffectiveSpec("s1"))));
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(NusmvResult.success("output", List.of(new SpecCheckResult("expr", false, null))));

        when(taskRepository.startTaskIfStillPending(anyLong(), any(), any(LocalDateTime.class), anyInt(), anyString(), any())).thenReturn(1);
        VerificationTaskPo task = VerificationTaskPo.builder()
                .id(9L).userId(1L).status(VerificationTaskPo.TaskStatus.RUNNING)
                .createdAt(LocalDateTime.now()).build();
        when(taskRepository.findById(9L)).thenReturn(Optional.of(task));

        service.verifyAsync(
                1L, 9L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 0, false));

        verify(taskRepository).completeTaskIfNotCancelled(
                eq(9L), eq(VerificationTaskPo.TaskStatus.COMPLETED), any(),
                eq(false), eq(1), eq(0), eq(0), any(), any(), any(), any(), any(), any());
    }

    @Test
    void verifyAsync_cancelledBeforeRun_skipsGeneration() throws Exception {
        cancelledTaskIds().add(8L);

        service.verifyAsync(
                1L, 8L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 0, false));

        verify(smvGenerator, never()).generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any());
    }

    @Test
    void verifyAsync_noLongerPending_skipsGeneration() throws Exception {
        // startTaskIfStillPending returns 0 by default (Mockito int stub),
        // simulating a DB-level race where the task was cancelled or started by another process
        // after the in-memory check passed.
        service.verifyAsync(
                1L, 11L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 0, false));

        // Verify the atomic start was attempted.
        verify(taskRepository).startTaskIfStillPending(
                eq(11L), eq(VerificationTaskPo.TaskStatus.RUNNING),
                any(LocalDateTime.class), eq(0), anyString(),
                eq(VerificationTaskPo.TaskStatus.PENDING));
        // Verify early return: findById for task loading should NOT be called after abort.
        // (updateTaskProgress may call findById(11L) before the atomic check, so we only
        // assert generate() was never reached.)
        verify(smvGenerator, never()).generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any());
    }

    @Test
    void verify_timeout_returnsTimedOutAndPurgesQueuedTask() {
        when(nusmvConfig.getTimeoutMs()).thenReturn(50L);
        Future<?> blocker = syncVerificationExecutor.submit(() -> {
            try {
                Thread.sleep(500);
            } catch (InterruptedException ignored) {
                Thread.currentThread().interrupt();
            }
        });

        VerificationResultDto result = service.verify(
                1L, makeRequest(singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")), false, 0, false));

        assertFalse(result.isSafe());
        assertTrue(result.getCheckLogs().stream().anyMatch(log -> log.contains("timed out")));

        ThreadPoolExecutor nativeExecutor = syncVerificationExecutor.getThreadPoolExecutor();
        assertNotNull(nativeExecutor);
        assertEquals(0, nativeExecutor.getQueue().size());
        blocker.cancel(true);
    }

    private SpecificationDto makeEffectiveSpec(String id) {
        SpecificationDto spec = new SpecificationDto();
        spec.setId(id);
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        SpecConditionDto cond = new SpecConditionDto();
        cond.setDeviceId("dev1");
        cond.setTargetType("state");
        cond.setKey("status");
        cond.setRelation("=");
        cond.setValue("on");
        spec.setAConditions(List.of(cond));
        spec.setIfConditions(List.of());
        spec.setThenConditions(List.of());
        return spec;
    }

    private RuleDto makeRule() {
        return RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor")
                        .attribute("state")
                        .relation("=")
                        .value("on")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("testDevice")
                        .action("turnOn")
                        .build())
                .build();
    }

    // ==================== terminal-state progress tests ====================

    @Test
    void cleanupStaleTasks_setsProgressTo100() throws Exception {
        VerificationTaskPo running = VerificationTaskPo.builder()
                .id(50L).userId(1L).status(VerificationTaskPo.TaskStatus.RUNNING)
                .createdAt(LocalDateTime.now()).build();
        VerificationTaskPo pending = VerificationTaskPo.builder()
                .id(51L).userId(1L).status(VerificationTaskPo.TaskStatus.PENDING)
                .createdAt(LocalDateTime.now()).build();

        when(taskRepository.findByStatusIn(
                List.of(VerificationTaskPo.TaskStatus.RUNNING, VerificationTaskPo.TaskStatus.PENDING)))
                .thenReturn(List.of(running, pending));

        // @PostConstruct is not invoked by plain constructor — call via reflection
        VerificationServiceImpl freshService = new VerificationServiceImpl(
                smvGenerator, smvTraceParser, nusmvExecutor, nusmvConfig,
                taskRepository, traceRepository, traceMapper,
                specificationMapper, verificationTaskMapper, new ObjectMapper(),
                verificationTaskExecutor, syncVerificationExecutor, null);
        Method cleanup = VerificationServiceImpl.class.getDeclaredMethod("cleanupStaleTasks");
        cleanup.setAccessible(true);
        cleanup.invoke(freshService);

        assertEquals(VerificationTaskPo.TaskStatus.FAILED, running.getStatus());
        assertEquals(100, running.getProgress());
        assertNotNull(running.getCompletedAt());

        assertEquals(VerificationTaskPo.TaskStatus.FAILED, pending.getStatus());
        assertEquals(100, pending.getProgress());
        assertNotNull(pending.getCompletedAt());
    }

    @Test
    void cancelTask_pendingTask_usesAtomicCancelUpdate() {
        VerificationTaskPo task = VerificationTaskPo.builder()
                .id(60L).userId(1L).status(VerificationTaskPo.TaskStatus.PENDING)
                .createdAt(LocalDateTime.now()).build();

        when(taskRepository.findByIdAndUserId(60L, 1L))
                .thenReturn(Optional.of(task));
        when(taskRepository.cancelTaskIfStillActive(
                eq(60L), eq(VerificationTaskPo.TaskStatus.CANCELLED), any(LocalDateTime.class), anyList()))
                .thenReturn(1);

        boolean result = service.cancelTask(1L, 60L);

        assertTrue(result);
        verify(taskRepository).cancelTaskIfStillActive(
                eq(60L), eq(VerificationTaskPo.TaskStatus.CANCELLED), any(LocalDateTime.class), anyList());
        assertFalse(wasTaskSaveCalled());
    }

    @Test
    void completeTask_skipsWhenAlreadyCancelledInDb() throws Exception {
        VerificationTaskPo task = VerificationTaskPo.builder()
                .id(70L).userId(1L).status(VerificationTaskPo.TaskStatus.RUNNING)
                .startedAt(LocalDateTime.now()).createdAt(LocalDateTime.now()).build();

        // Atomic UPDATE returns 0 — task was already cancelled in DB
        when(taskRepository.completeTaskIfNotCancelled(
                eq(70L), any(), any(), anyBoolean(), anyInt(),
                anyInt(), anyInt(), any(), any(), any(), any(), any(), any()))
                .thenReturn(0);

        Method completeTask = VerificationServiceImpl.class.getDeclaredMethod(
                "completeTask", VerificationTaskPo.class, boolean.class, int.class,
                List.class, List.class, String.class, int.class, int.class);
        completeTask.setAccessible(true);
        completeTask.invoke(service, task, true, 0,
                List.of(SpecResultDto.builder().specId("s1").passed(true).expression("expr").build()),
                List.of("done"), "", 1, 2);

        // Atomic UPDATE was called (returns 0 = no rows affected = already cancelled)
        verify(taskRepository).completeTaskIfNotCancelled(
                eq(70L), any(), any(), anyBoolean(), anyInt(),
                eq(1), eq(2), eq("[{\"specId\":\"s1\",\"passed\":true,\"expression\":\"expr\"}]"),
                any(), any(), any(), any(), any());
        // save() should NOT be called — atomic UPDATE replaces it
        assertFalse(wasTaskSaveCalled());
    }

    @Test
    void failTask_skipsWhenAlreadyCancelledInDb() throws Exception {
        VerificationTaskPo task = VerificationTaskPo.builder()
                .id(71L).userId(1L).status(VerificationTaskPo.TaskStatus.RUNNING)
                .startedAt(LocalDateTime.now()).createdAt(LocalDateTime.now()).build();

        // Atomic UPDATE returns 0 — task was already cancelled in DB
        when(taskRepository.failTaskIfNotCancelled(
                eq(71L), any(), any(), any(), any(), any(), any()))
                .thenReturn(0);

        Method failTask = VerificationServiceImpl.class.getDeclaredMethod(
                "failTask", VerificationTaskPo.class, String.class);
        failTask.setAccessible(true);
        failTask.invoke(service, task, "some error");

        // Atomic UPDATE was called (returns 0 = no rows affected = already cancelled)
        verify(taskRepository).failTaskIfNotCancelled(
                eq(71L), any(), any(), any(), any(), any(), any());
        // save() should NOT be called — atomic UPDATE replaces it
        assertFalse(wasTaskSaveCalled());
    }

    private boolean wasTaskSaveCalled() {
        return mockingDetails(taskRepository).getInvocations().stream()
                .anyMatch(invocation -> invocation.getMethod().getName().equals("save"));
    }

    private void assertSpecResult(SpecResultDto result, String specId, boolean passed, String expression) {
        assertEquals(specId, result.getSpecId());
        assertEquals(passed, result.isPassed());
        assertEquals(expression, result.getExpression());
    }

    private VerificationRequestDto makeRequest(List<DeviceVerificationDto> devices, List<RuleDto> rules,
                                                List<SpecificationDto> specs, boolean isAttack,
                                                int intensity, boolean enablePrivacy) {
        VerificationRequestDto r = new VerificationRequestDto();
        r.setDevices(devices);
        r.setRules(rules);
        r.setSpecs(specs);
        r.setAttack(isAttack);
        r.setIntensity(intensity);
        r.setEnablePrivacy(enablePrivacy);
        return r;
    }
}
