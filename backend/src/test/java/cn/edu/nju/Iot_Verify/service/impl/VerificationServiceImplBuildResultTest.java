package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;

import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
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

    private VerificationServiceImpl service;
    private ThreadPoolTaskExecutor syncVerificationExecutor;
    private Method buildVerificationResult;

    @BeforeEach
    void setUp() throws Exception {
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
                syncVerificationExecutor);

        buildVerificationResult = VerificationServiceImpl.class.getDeclaredMethod(
                "buildVerificationResult",
                NusmvResult.class, List.class, List.class, List.class,
                Long.class, Long.class, List.class, Map.class);
        buildVerificationResult.setAccessible(true);
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
                service, result, devices, List.of(), specs, 1L, null, checkLogs, Map.of());
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

    @SuppressWarnings("unchecked")
    private Set<Long> cancelledTaskIds() throws Exception {
        Field f = VerificationServiceImpl.class.getDeclaredField("cancelledTasks");
        f.setAccessible(true);
        return (Set<Long>) f.get(service);
    }

    // --- effectiveSpecs = 0: all specs filtered out -> safe=true ---

    @Test
    void effectiveSpecsEmpty_returnsSafeTrue() throws Exception {
        // Spec with no A/IF conditions -> filtered out
        SpecificationDto emptySpec = new SpecificationDto();
        emptySpec.setId("s1");
        emptySpec.setAConditions(List.of());
        emptySpec.setIfConditions(List.of());

        NusmvResult result = NusmvResult.success("", List.of());
        List<String> logs = new ArrayList<>();

        VerificationResultDto dto = invoke(result, List.of(), List.of(emptySpec), logs);

        assertTrue(dto.isSafe());
        assertTrue(dto.getSpecResults().isEmpty());
        assertTrue(logs.stream().anyMatch(l -> l.contains("No valid specifications")));
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
        assertFalse(dto.getSpecResults().get(0));
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
        assertTrue(dto.getSpecResults().get(0));   // first result preserved
        assertFalse(dto.getSpecResults().get(1));  // missing -> false
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
        assertTrue(dto.getSpecResults().get(0));
    }

    @Test
    void verify_executorRejected_throwsServiceUnavailable() {
        syncVerificationExecutor.shutdown();

        ServiceUnavailableException ex = assertThrows(ServiceUnavailableException.class,
                () -> service.verify(
                        1L, singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")),
                        false, 0, false));
        assertTrue(ex.getMessage().contains("busy"));
    }

    @Test
    void verify_nusmvBusy_throwsServiceUnavailable() throws Exception {
        when(nusmvConfig.getTimeoutMs()).thenReturn(1000L);
        File smv = createTempModelFile();
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any()))
                .thenReturn(new SmvGenerator.GenerateResult(smv, Map.of()));
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(NusmvResult.busy("NuSMV execution is busy, please retry later"));

        ServiceUnavailableException ex = assertThrows(ServiceUnavailableException.class,
                () -> service.verify(
                        1L, singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")),
                        false, 0, false));
        assertTrue(ex.getMessage().contains("busy"));
        assertEquals(503, readResultCode(smv));
    }

    @Test
    void verify_smvGenerationError_rethrowsSmvGenerationException() throws Exception {
        when(nusmvConfig.getTimeoutMs()).thenReturn(1000L);
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any()))
                .thenThrow(SmvGenerationException.ambiguousDeviceReference("Sensor", List.of("sensor_1", "sensor_2")));

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> service.verify(
                        1L, singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")),
                        false, 0, false));
        assertEquals("AMBIGUOUS_DEVICE_REFERENCE", ex.getErrorCategory());
    }

    @Test
    void verifyAsync_success_writesResultJson() throws Exception {
        File smv = createTempModelFile();
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(), anyBoolean(), anyInt(), anyBoolean(), any()))
                .thenReturn(new SmvGenerator.GenerateResult(smv, Map.of()));
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(NusmvResult.success("output", List.of(new SpecCheckResult("expr", true, null))));

        VerificationTaskPo task = VerificationTaskPo.builder()
                .id(7L)
                .userId(1L)
                .status(VerificationTaskPo.TaskStatus.PENDING)
                .createdAt(LocalDateTime.now())
                .build();
        when(taskRepository.findById(7L)).thenReturn(Optional.of(task));
        when(taskRepository.save(any(VerificationTaskPo.class))).thenAnswer(inv -> inv.getArgument(0));

        service.verifyAsync(
                1L, 7L, singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")),
                false, 0, false);

        assertEquals(200, readResultCode(smv));
    }

    @Test
    void verifyAsync_cancelledBeforeRun_skipsGeneration() throws Exception {
        VerificationTaskPo task = VerificationTaskPo.builder()
                .id(8L)
                .userId(1L)
                .status(VerificationTaskPo.TaskStatus.PENDING)
                .createdAt(LocalDateTime.now())
                .build();
        when(taskRepository.findById(8L)).thenReturn(Optional.of(task));
        cancelledTaskIds().add(8L);

        service.verifyAsync(
                1L, 8L, singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")),
                false, 0, false);

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
                1L, singleDevice(), List.of(), List.of(makeEffectiveSpec("s1")),
                false, 0, false);

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
}
