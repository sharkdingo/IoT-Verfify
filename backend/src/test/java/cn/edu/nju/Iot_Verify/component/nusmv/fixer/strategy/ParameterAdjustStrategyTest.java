package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixContext;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize.ParameterizationConfig;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.fix.ParameterAdjustment;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class ParameterAdjustStrategyTest {

    @Mock private SmvGenerator smvGenerator;
    @Mock private NusmvExecutor nusmvExecutor;

    private ParameterAdjustStrategy strategy;

    @BeforeEach
    void setUp() {
        FixConfig fixConfig = new FixConfig();
        fixConfig.setMaxRefineAttempts(10);
        strategy = new ParameterAdjustStrategy(smvGenerator, nusmvExecutor, fixConfig);
    }

    private SmvGenerator.GenerateResult createGenResult() throws IOException {
        File tempDir = Files.createTempDirectory("smv-test").toFile();
        File smvFile = new File(tempDir, "test.smv");
        smvFile.createNewFile();
        return new SmvGenerator.GenerateResult(smvFile, Map.of());
    }

    private Map<String, DeviceSmvData> buildDeviceMap() {
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName("sensor_1");
        smv.setModuleName("SensorModule");
        DeviceManifest.InternalVariable tempVar = DeviceManifest.InternalVariable.builder()
                .name("temperature")
                .lowerBound(0)
                .upperBound(50)
                .build();
        smv.setVariables(List.of(tempVar));
        return Map.of("sensor_1", smv);
    }

    private FixContext ctx(List<FaultRuleDto> faultRules, List<RuleDto> allRules,
                            List<SpecificationDto> specs, Map<String, DeviceSmvData> deviceSmvMap) {
        return FixContext.builder()
                .faultRules(faultRules)
                .allRules(allRules)
                .devices(List.of())
                .specs(specs)
                .deviceSmvMap(deviceSmvMap)
                .violatedSpecIndex(0)
                .userId(1L)
                .isAttack(false)
                .intensity(0)
                .enablePrivacy(false)
                .maxAttempts(20)
                .build();
    }

    @Test
    void tryFix_nullFaultRules_returnsNull() {
        assertNull(strategy.tryFix(ctx(null, List.of(), List.of(), Map.of())));
    }

    @Test
    void tryFix_emptyFaultRules_returnsNull() {
        assertNull(strategy.tryFix(ctx(List.of(), List.of(), List.of(), Map.of())));
    }

    @Test
    void tryFix_noNumericConditions_returnsNull() {
        // Rule with state condition (non-numeric) — should not be parameterizable
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("state").relation("=").value("active").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        assertNull(strategy.tryFix(ctx(List.of(fault), List.of(rule), List.of(spec), buildDeviceMap())));
    }

    @Test
    void tryFix_numericCondition_negatedSpecTrue_returnsNull() throws Exception {
        // Setup: numeric condition with bounds available
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), any(ParameterizationConfig.class)))
                .thenReturn(createGenResult());

        // Negated spec passes (universally true) → no fix possible
        SpecCheckResult passing = mock(SpecCheckResult.class);
        when(passing.isPassed()).thenReturn(true);
        NusmvResult result = mock(NusmvResult.class);
        when(result.isSuccess()).thenReturn(true);
        when(result.getSpecResults()).thenReturn(List.of(passing));
        when(nusmvExecutor.execute(any(File.class))).thenReturn(result);

        assertNull(strategy.tryFix(ctx(List.of(fault), List.of(rule), List.of(spec), buildDeviceMap())));
    }

    @Test
    void tryFix_numericCondition_findsFixValue() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        // generateParameterized: called for initial discovery AND refinement NuSMV solves
        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), any(ParameterizationConfig.class)))
                .thenReturn(createGenResult());

        // generate: called for forward-verify (initial, try-original, candidate verify)
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(createGenResult());

        // NuSMV counterexample outputs
        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult negatedResult25 = mock(NusmvResult.class);
        when(negatedResult25.isSuccess()).thenReturn(true);
        when(negatedResult25.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult25.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 25\n    sensor_1.temperature = 30\n");

        NusmvResult negatedResult29 = mock(NusmvResult.class);
        when(negatedResult29.isSuccess()).thenReturn(true);
        when(negatedResult29.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult29.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 29\n");

        // Forward-verify results
        SpecCheckResult allPass = mock(SpecCheckResult.class);
        when(allPass.isPassed()).thenReturn(true);
        NusmvResult verifyPass = mock(NusmvResult.class);
        when(verifyPass.isSuccess()).thenReturn(true);
        when(verifyPass.getSpecResults()).thenReturn(List.of(allPass));

        SpecCheckResult allFail = mock(SpecCheckResult.class);
        when(allFail.isPassed()).thenReturn(false);
        NusmvResult verifyFail = mock(NusmvResult.class);
        when(verifyFail.isSuccess()).thenReturn(true);
        when(verifyFail.getSpecResults()).thenReturn(List.of(allFail));

        // execute() call sequence:
        // 1. negatedResult25        → initial discovery (param=25)
        // 2. verifyPass             → initial forward-verify passes
        // 3. verifyFail             → try-original (param=30) fails
        // 4. negatedResult29        → refinement NuSMV solve → param=29
        // 5. verifyPass             → candidate 29 forward-verify passes
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(negatedResult25)
                .thenReturn(verifyPass)
                .thenReturn(verifyFail)
                .thenReturn(negatedResult29)
                .thenReturn(verifyPass);

        FixSuggestionDto suggestion = strategy.tryFix(
                ctx(List.of(fault), List.of(rule), List.of(spec), buildDeviceMap()));

        assertNotNull(suggestion);
        assertEquals("parameter", suggestion.getStrategy());
        assertTrue(suggestion.isVerified());
        assertNotNull(suggestion.getParameterAdjustments());
        assertEquals(1, suggestion.getParameterAdjustments().size());
        // NuSMV-guided refinement: initial=25, try-original(30) fails,
        // NuSMV finds 29 in distance-bounded range, forward-verify passes → bestDist=1 → done
        assertEquals("29", suggestion.getParameterAdjustments().get(0).getNewValue());
        assertEquals("30", suggestion.getParameterAdjustments().get(0).getOriginalValue());
    }

    @Test
    void tryFix_refine_tryOriginalWorks_returnsOriginal() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), any(ParameterizationConfig.class)))
                .thenReturn(createGenResult());
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(createGenResult());

        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult negatedResult = mock(NusmvResult.class);
        when(negatedResult.isSuccess()).thenReturn(true);
        when(negatedResult.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 25\n");

        SpecCheckResult allPass = mock(SpecCheckResult.class);
        when(allPass.isPassed()).thenReturn(true);
        NusmvResult verifyPass = mock(NusmvResult.class);
        when(verifyPass.isSuccess()).thenReturn(true);
        when(verifyPass.getSpecResults()).thenReturn(List.of(allPass));

        // 1. negatedResult → initial discovery (param=25)
        // 2. verifyPass    → initial forward-verify
        // 3. verifyPass    → try-original (param=30) PASSES → distance=0, skip NuSMV loop
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(negatedResult)
                .thenReturn(verifyPass)
                .thenReturn(verifyPass);

        FixSuggestionDto suggestion = strategy.tryFix(
                ctx(List.of(fault), List.of(rule), List.of(spec), buildDeviceMap()));

        assertNotNull(suggestion);
        // Original value works with other params fixed → distance 0
        assertEquals("30", suggestion.getParameterAdjustments().get(0).getNewValue());
    }

    @Test
    void tryFix_refine_unsat_keepsInitialValue() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), any(ParameterizationConfig.class)))
                .thenReturn(createGenResult());
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(createGenResult());

        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult negatedResult = mock(NusmvResult.class);
        when(negatedResult.isSuccess()).thenReturn(true);
        when(negatedResult.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 25\n");

        SpecCheckResult allPass = mock(SpecCheckResult.class);
        when(allPass.isPassed()).thenReturn(true);
        NusmvResult verifyPass = mock(NusmvResult.class);
        when(verifyPass.isSuccess()).thenReturn(true);
        when(verifyPass.getSpecResults()).thenReturn(List.of(allPass));

        // UNSAT result for refinement (¬ρ universally true in distance range)
        SpecCheckResult unsatPass = mock(SpecCheckResult.class);
        when(unsatPass.isPassed()).thenReturn(true);
        NusmvResult unsatResult = mock(NusmvResult.class);
        when(unsatResult.isSuccess()).thenReturn(true);
        when(unsatResult.getSpecResults()).thenReturn(List.of(unsatPass));

        // 1. negatedResult → discovery (param=25)
        // 2. verifyPass    → initial forward-verify
        // 3. verifyPass    → try-original fails (use allFail below)
        NusmvResult verifyFail = mock(NusmvResult.class);
        when(verifyFail.isSuccess()).thenReturn(true);
        SpecCheckResult specFail = mock(SpecCheckResult.class);
        when(specFail.isPassed()).thenReturn(false);
        when(verifyFail.getSpecResults()).thenReturn(List.of(specFail));

        // 4. unsatResult   → refinement UNSAT → break, keep initial value 25
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(negatedResult)
                .thenReturn(verifyPass)
                .thenReturn(verifyFail)
                .thenReturn(unsatResult);

        FixSuggestionDto suggestion = strategy.tryFix(
                ctx(List.of(fault), List.of(rule), List.of(spec), buildDeviceMap()));

        assertNotNull(suggestion);
        assertEquals("25", suggestion.getParameterAdjustments().get(0).getNewValue());
    }

    @Test
    void tryFix_refine_tryOriginalTransientFailure_recoveredViaLoop() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        ArgumentCaptor<ParameterizationConfig> configCaptor =
                ArgumentCaptor.forClass(ParameterizationConfig.class);
        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), configCaptor.capture()))
                .thenReturn(createGenResult());
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(createGenResult());

        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult negatedResult25 = mock(NusmvResult.class);
        when(negatedResult25.isSuccess()).thenReturn(true);
        when(negatedResult25.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult25.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 25\n");

        // NuSMV re-discovers original value 30 in the refinement loop
        NusmvResult negatedResult30 = mock(NusmvResult.class);
        when(negatedResult30.isSuccess()).thenReturn(true);
        when(negatedResult30.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult30.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 30\n");

        SpecCheckResult allPass = mock(SpecCheckResult.class);
        when(allPass.isPassed()).thenReturn(true);
        NusmvResult verifyPass = mock(NusmvResult.class);
        when(verifyPass.isSuccess()).thenReturn(true);
        when(verifyPass.getSpecResults()).thenReturn(List.of(allPass));

        // Transient NuSMV crash during try-original forward-verify
        NusmvResult crashResult = mock(NusmvResult.class);
        when(crashResult.isSuccess()).thenReturn(false);
        when(crashResult.getErrorMessage()).thenReturn("NuSMV process crashed");

        // 1. negatedResult25  → discovery (param=25, original=30, distance=5)
        // 2. verifyPass       → initial forward-verify passes
        // 3. crashResult      → try-original: NuSMV crash (transient) → forwardVerify=false
        //    (original NOT excluded — key behavior change from this fix)
        // 4. negatedResult30  → refinement: NuSMV re-discovers original=30!
        // 5. verifyPass       → candidate 30 forward-verify passes → distance=0 recovered
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(negatedResult25)
                .thenReturn(verifyPass)
                .thenReturn(crashResult)
                .thenReturn(negatedResult30)
                .thenReturn(verifyPass);

        FixSuggestionDto suggestion = strategy.tryFix(
                ctx(List.of(fault), List.of(rule), List.of(spec), buildDeviceMap()));

        assertNotNull(suggestion);
        // Core assertion: original value recovered via loop despite try-original transient failure
        assertEquals("30", suggestion.getParameterAdjustments().get(0).getNewValue());
        assertEquals("30", suggestion.getParameterAdjustments().get(0).getOriginalValue());

        // Regression guard: verify refinement exclusionInvars do NOT exclude original.
        // Locate refinement config by non-empty exclusionInvars (initial discovery has none).
        List<ParameterizationConfig> allConfigs = configCaptor.getAllValues();
        ParameterizationConfig refinementConfig = allConfigs.stream()
                .filter(c -> c.getExclusionInvars() != null && !c.getExclusionInvars().isEmpty())
                .findFirst()
                .orElseThrow(() -> new AssertionError("no refinement config with exclusionInvars found"));
        List<String> exclusions = refinementConfig.getExclusionInvars();
        assertFalse(exclusions.contains("!(param_r0_c0=30)"),
                "original value must NOT be excluded — enables transient-failure recovery");
        assertTrue(exclusions.contains("!(param_r0_c0=25)"),
                "initial discovery value must be excluded");
    }

    @Test
    void tryFix_refine_originalCandidate_transientVerifyFail_allowsRetry() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        ArgumentCaptor<ParameterizationConfig> configCaptor =
                ArgumentCaptor.forClass(ParameterizationConfig.class);
        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), configCaptor.capture()))
                .thenReturn(createGenResult());
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(createGenResult());

        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult negatedResult25 = mock(NusmvResult.class);
        when(negatedResult25.isSuccess()).thenReturn(true);
        when(negatedResult25.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult25.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 25\n");

        NusmvResult negatedResult30 = mock(NusmvResult.class);
        when(negatedResult30.isSuccess()).thenReturn(true);
        when(negatedResult30.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult30.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 30\n");

        SpecCheckResult allPass = mock(SpecCheckResult.class);
        when(allPass.isPassed()).thenReturn(true);
        NusmvResult verifyPass = mock(NusmvResult.class);
        when(verifyPass.isSuccess()).thenReturn(true);
        when(verifyPass.getSpecResults()).thenReturn(List.of(allPass));

        NusmvResult crashResult = mock(NusmvResult.class);
        when(crashResult.isSuccess()).thenReturn(false);
        when(crashResult.getErrorMessage()).thenReturn("NuSMV process crashed");

        // Double-transient scenario:
        // 1. negatedResult25  → discovery (param=25, original=30, distance=5)
        // 2. verifyPass       → initial forward-verify
        // 3. crashResult      → try-original: transient crash #1
        // 4. negatedResult30  → refinement: NuSMV returns original=30
        // 5. crashResult      → candidate 30 forward-verify: transient crash #2
        //    (originalRetried flag: un-exclude 30 from exclusionValues/seen)
        // 6. negatedResult30  → refinement: NuSMV returns original=30 AGAIN (not excluded!)
        // 7. verifyPass       → candidate 30 forward-verify: succeeds → distance=0
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(negatedResult25)
                .thenReturn(verifyPass)
                .thenReturn(crashResult)
                .thenReturn(negatedResult30)
                .thenReturn(crashResult)
                .thenReturn(negatedResult30)
                .thenReturn(verifyPass);

        FixSuggestionDto suggestion = strategy.tryFix(
                ctx(List.of(fault), List.of(rule), List.of(spec), buildDeviceMap()));

        assertNotNull(suggestion);
        // Core: double-transient recovered on third attempt via originalRetried flag
        assertEquals("30", suggestion.getParameterAdjustments().get(0).getNewValue());

        // Regression guard: refinement call after un-exclude must NOT have !(param_r0_c0=30)
        List<ParameterizationConfig> allConfigs = configCaptor.getAllValues();
        // Last generateParameterized call is the retry (step 6)
        ParameterizationConfig retryConfig = allConfigs.get(allConfigs.size() - 1);
        List<String> exclusions = retryConfig.getExclusionInvars();
        assertFalse(exclusions.contains("!(param_r0_c0=30)"),
                "original must be un-excluded after transient verify failure");
    }

    @Test
    void tryFix_refine_consecutiveErrors_exits() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), any(ParameterizationConfig.class)))
                .thenReturn(createGenResult());
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(createGenResult());

        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult negatedResult = mock(NusmvResult.class);
        when(negatedResult.isSuccess()).thenReturn(true);
        when(negatedResult.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 25\n");

        SpecCheckResult allPass = mock(SpecCheckResult.class);
        when(allPass.isPassed()).thenReturn(true);
        NusmvResult verifyPass = mock(NusmvResult.class);
        when(verifyPass.isSuccess()).thenReturn(true);
        when(verifyPass.getSpecResults()).thenReturn(List.of(allPass));

        SpecCheckResult specFail = mock(SpecCheckResult.class);
        when(specFail.isPassed()).thenReturn(false);
        NusmvResult verifyFail = mock(NusmvResult.class);
        when(verifyFail.isSuccess()).thenReturn(true);
        when(verifyFail.getSpecResults()).thenReturn(List.of(specFail));

        NusmvResult errorResult = mock(NusmvResult.class);
        when(errorResult.isSuccess()).thenReturn(false);
        when(errorResult.getErrorMessage()).thenReturn("NuSMV crashed");

        // 1. negatedResult → discovery (param=25)
        // 2. verifyPass    → initial forward-verify
        // 3. verifyFail    → try-original fails
        // 4. errorResult   → refinement ERROR #1
        // 5. errorResult   → refinement ERROR #2
        // 6. errorResult   → refinement ERROR #3 → consecutiveErrors>=3, break
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(negatedResult)
                .thenReturn(verifyPass)
                .thenReturn(verifyFail)
                .thenReturn(errorResult)
                .thenReturn(errorResult)
                .thenReturn(errorResult);

        FixSuggestionDto suggestion = strategy.tryFix(
                ctx(List.of(fault), List.of(rule), List.of(spec), buildDeviceMap()));

        assertNotNull(suggestion);
        // 3 consecutive errors → exits refinement, keeps initial value 25
        assertEquals("25", suggestion.getParameterAdjustments().get(0).getNewValue());
    }

    @Test
    void tryFix_refine_outOfBoundsCandidate_treatedAsError() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), any(ParameterizationConfig.class)))
                .thenReturn(createGenResult());
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(createGenResult());

        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult negatedResult = mock(NusmvResult.class);
        when(negatedResult.isSuccess()).thenReturn(true);
        when(negatedResult.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 25\n");

        // Out-of-bounds: NuSMV returns 999, but refined range is [26,34]
        NusmvResult outOfBoundsResult = mock(NusmvResult.class);
        when(outOfBoundsResult.isSuccess()).thenReturn(true);
        when(outOfBoundsResult.getSpecResults()).thenReturn(List.of(failing));
        when(outOfBoundsResult.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 999\n");

        SpecCheckResult unsatPass = mock(SpecCheckResult.class);
        when(unsatPass.isPassed()).thenReturn(true);
        NusmvResult unsatResult = mock(NusmvResult.class);
        when(unsatResult.isSuccess()).thenReturn(true);
        when(unsatResult.getSpecResults()).thenReturn(List.of(unsatPass));

        SpecCheckResult allPass = mock(SpecCheckResult.class);
        when(allPass.isPassed()).thenReturn(true);
        NusmvResult verifyPass = mock(NusmvResult.class);
        when(verifyPass.isSuccess()).thenReturn(true);
        when(verifyPass.getSpecResults()).thenReturn(List.of(allPass));

        SpecCheckResult specFail = mock(SpecCheckResult.class);
        when(specFail.isPassed()).thenReturn(false);
        NusmvResult verifyFail = mock(NusmvResult.class);
        when(verifyFail.isSuccess()).thenReturn(true);
        when(verifyFail.getSpecResults()).thenReturn(List.of(specFail));

        // 1. negatedResult      → discovery (param=25, original=30, distance=5)
        // 2. verifyPass         → initial forward-verify
        // 3. verifyFail         → try-original fails
        // 4. outOfBoundsResult  → refinement: param=999 outside [26,34] → ERROR
        // 5. unsatResult        → refinement: UNSAT → break
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(negatedResult)
                .thenReturn(verifyPass)
                .thenReturn(verifyFail)
                .thenReturn(outOfBoundsResult)
                .thenReturn(unsatResult);

        FixSuggestionDto suggestion = strategy.tryFix(
                ctx(List.of(fault), List.of(rule), List.of(spec), buildDeviceMap()));

        assertNotNull(suggestion);
        // Out-of-bounds treated as error, then UNSAT → keeps initial value 25
        assertEquals("25", suggestion.getParameterAdjustments().get(0).getNewValue());
    }

    @Test
    void tryFix_refine_duplicateCandidate_skipsForwardVerify() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), any(ParameterizationConfig.class)))
                .thenReturn(createGenResult());
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(createGenResult());

        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult negatedResult25 = mock(NusmvResult.class);
        when(negatedResult25.isSuccess()).thenReturn(true);
        when(negatedResult25.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult25.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 25\n");

        NusmvResult negatedResult28 = mock(NusmvResult.class);
        when(negatedResult28.isSuccess()).thenReturn(true);
        when(negatedResult28.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult28.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 28\n");

        SpecCheckResult allPass = mock(SpecCheckResult.class);
        when(allPass.isPassed()).thenReturn(true);
        NusmvResult verifyPass = mock(NusmvResult.class);
        when(verifyPass.isSuccess()).thenReturn(true);
        when(verifyPass.getSpecResults()).thenReturn(List.of(allPass));

        SpecCheckResult specFail = mock(SpecCheckResult.class);
        when(specFail.isPassed()).thenReturn(false);
        NusmvResult verifyFail = mock(NusmvResult.class);
        when(verifyFail.isSuccess()).thenReturn(true);
        when(verifyFail.getSpecResults()).thenReturn(List.of(specFail));

        SpecCheckResult unsatPass = mock(SpecCheckResult.class);
        when(unsatPass.isPassed()).thenReturn(true);
        NusmvResult unsatResult = mock(NusmvResult.class);
        when(unsatResult.isSuccess()).thenReturn(true);
        when(unsatResult.getSpecResults()).thenReturn(List.of(unsatPass));

        // 1. negatedResult25  → discovery (param=25)
        // 2. verifyPass       → initial forward-verify
        // 3. verifyFail       → try-original fails
        // 4. negatedResult28  → refinement candidate=28
        // 5. verifyFail       → candidate 28 forward-verify fails
        // 6. negatedResult28  → duplicate 28 → seen.contains(28)=true, skip forward-verify
        // 7. unsatResult      → UNSAT → break
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(negatedResult25)
                .thenReturn(verifyPass)
                .thenReturn(verifyFail)
                .thenReturn(negatedResult28)
                .thenReturn(verifyFail)
                .thenReturn(negatedResult28)
                .thenReturn(unsatResult);

        FixSuggestionDto suggestion = strategy.tryFix(
                ctx(List.of(fault), List.of(rule), List.of(spec), buildDeviceMap()));

        assertNotNull(suggestion);
        assertEquals("25", suggestion.getParameterAdjustments().get(0).getNewValue());
        // generate() = forward-verify calls: initial + try-original + candidate 28 (once) = 3
        // If dedup failed, would be 4 (candidate 28 verified twice)
        verify(smvGenerator, times(3)).generate(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean());
    }

    @Test
    void tryFix_nusmvFailure_exhaustsAttemptsAndReturnsNull() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), any(ParameterizationConfig.class)))
                .thenReturn(createGenResult());

        NusmvResult failedResult = mock(NusmvResult.class);
        when(failedResult.isSuccess()).thenReturn(false);
        when(failedResult.getErrorMessage()).thenReturn("NuSMV crashed");
        when(nusmvExecutor.execute(any(File.class))).thenReturn(failedResult);

        // Use maxAttempts=3 to verify retry behavior
        FixContext context = FixContext.builder()
                .faultRules(List.of(fault))
                .allRules(List.of(rule))
                .devices(List.of())
                .specs(List.of(spec))
                .deviceSmvMap(buildDeviceMap())
                .violatedSpecIndex(0)
                .userId(1L)
                .isAttack(false)
                .intensity(0)
                .enablePrivacy(false)
                .maxAttempts(3)
                .build();

        assertNull(strategy.tryFix(context));
        // Verify it retried all 3 attempts before giving up
        verify(nusmvExecutor, times(3)).execute(any(File.class));
    }

    // ---- P3: preferred range tests ----

    @Test
    void tryFix_preferredRange_narrowsBounds() throws Exception {
        // Use maxRefineAttempts=0 to skip refinement and test bounds narrowing only
        FixConfig noRefineConfig = new FixConfig();
        noRefineConfig.setMaxRefineAttempts(0);
        ParameterAdjustStrategy noRefineStrategy =
                new ParameterAdjustStrategy(smvGenerator, nusmvExecutor, noRefineConfig);

        // Template bounds [0,50], preferred [20,30] → intersection [20,30]
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        // Capture the ParameterizationConfig to verify bounds
        ArgumentCaptor<ParameterizationConfig> configCaptor =
                ArgumentCaptor.forClass(ParameterizationConfig.class);
        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), configCaptor.capture()))
                .thenReturn(createGenResult());

        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult negatedResult = mock(NusmvResult.class);
        when(negatedResult.isSuccess()).thenReturn(true);
        when(negatedResult.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    param_r0_c0 = 25\n");

        SmvGenerator.GenerateResult verifyGenResult = createGenResult();
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(verifyGenResult);

        SpecCheckResult allPass = mock(SpecCheckResult.class);
        when(allPass.isPassed()).thenReturn(true);
        NusmvResult verifyResult = mock(NusmvResult.class);
        when(verifyResult.isSuccess()).thenReturn(true);
        when(verifyResult.getSpecResults()).thenReturn(List.of(allPass));

        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(negatedResult)
                .thenReturn(verifyResult);

        FixContext context = FixContext.builder()
                .faultRules(List.of(fault))
                .allRules(List.of(rule))
                .devices(List.of())
                .specs(List.of(spec))
                .deviceSmvMap(buildDeviceMap())
                .violatedSpecIndex(0)
                .userId(1L)
                .isAttack(false)
                .intensity(0)
                .enablePrivacy(false)
                .maxAttempts(20)
                .preferredRanges(Map.of("r0_c0", new PreferredRange(20, 30)))
                .build();

        FixSuggestionDto suggestion = noRefineStrategy.tryFix(context);
        assertNotNull(suggestion);

        // Verify the ParamInfo bounds were narrowed to [20,30]
        ParameterizationConfig captured = configCaptor.getValue();
        ParameterizationConfig.ParamInfo paramInfo = captured.getParameterizedThresholds().get("r0_c0");
        assertNotNull(paramInfo);
        assertEquals(20, paramInfo.getLowerBound());
        assertEquals(30, paramInfo.getUpperBound());

        // Verify the adjustment also has narrowed bounds
        assertEquals(1, suggestion.getParameterAdjustments().size());
        ParameterAdjustment adj = suggestion.getParameterAdjustments().get(0);
        assertEquals(20, adj.getLowerBound());
        assertEquals(30, adj.getUpperBound());
    }

    @Test
    void tryFix_preferredRange_noIntersection_skipsParam() {
        // Template bounds [0,50], preferred [60,70] → no intersection, skip
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        FixContext context = FixContext.builder()
                .faultRules(List.of(fault))
                .allRules(List.of(rule))
                .devices(List.of())
                .specs(List.of(spec))
                .deviceSmvMap(buildDeviceMap())
                .violatedSpecIndex(0)
                .userId(1L)
                .isAttack(false)
                .intensity(0)
                .enablePrivacy(false)
                .maxAttempts(20)
                .preferredRanges(Map.of("r0_c0", new PreferredRange(60, 70)))
                .build();

        // Should return null because the only parameterizable condition was skipped
        assertNull(strategy.tryFix(context));
    }
}
