package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixContext;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize.ParameterizationConfig;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
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
class ConditionAdjustStrategyTest {

    @Mock private SmvGenerator smvGenerator;
    @Mock private NusmvExecutor nusmvExecutor;

    private ConditionAdjustStrategy strategy;

    @BeforeEach
    void setUp() {
        FixConfig fixConfig = new FixConfig();
        fixConfig.setMaxCandidatesPerRule(5);
        strategy = new ConditionAdjustStrategy(smvGenerator, nusmvExecutor, fixConfig);
    }

    private SmvGenerator.GenerateResult createGenResult() throws IOException {
        File tempDir = Files.createTempDirectory("smv-test").toFile();
        File smvFile = new File(tempDir, "test.smv");
        smvFile.createNewFile();
        return new SmvGenerator.GenerateResult(smvFile, Map.of());
    }

    private FixContext ctx(List<FaultRuleDto> faultRules, List<RuleDto> allRules,
                            List<SpecificationDto> specs) {
        return FixContext.builder()
                .faultRules(faultRules)
                .allRules(allRules)
                .devices(List.of())
                .specs(specs)
                .deviceSmvMap(Map.of())
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
        assertNull(strategy.tryFix(ctx(null, List.of(), List.of())));
    }

    @Test
    void tryFix_emptyFaultRules_returnsNull() {
        assertNull(strategy.tryFix(ctx(List.of(), List.of(), List.of())));
    }

    @Test
    void tryFix_negatedSpecTrue_returnsNull() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(
                        RuleDto.Condition.builder()
                                .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build(),
                        RuleDto.Condition.builder()
                                .deviceName("sensor_1").attribute("humidity").relation(">").value("60").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), any(ParameterizationConfig.class)))
                .thenReturn(createGenResult());

        // Negated spec universally true → no fix
        SpecCheckResult passing = mock(SpecCheckResult.class);
        when(passing.isPassed()).thenReturn(true);
        NusmvResult result = mock(NusmvResult.class);
        when(result.isSuccess()).thenReturn(true);
        when(result.getSpecResults()).thenReturn(List.of(passing));
        when(nusmvExecutor.execute(any(File.class))).thenReturn(result);

        assertNull(strategy.tryFix(ctx(List.of(fault), List.of(rule), List.of(spec))));
    }

    @Test
    void tryFix_removesCondition_fixesViolation() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(
                        RuleDto.Condition.builder()
                                .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build(),
                        RuleDto.Condition.builder()
                                .deviceName("sensor_1").attribute("humidity").relation(">").value("60").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("turnOn").build())
                .build();
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");

        // Parameterized model generation
        when(smvGenerator.generateParameterized(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean(), any(ParameterizationConfig.class)))
                .thenReturn(createGenResult());

        // NuSMV returns counterexample: lambda_r0_c0 = TRUE (keep), lambda_r0_c1 = FALSE (remove)
        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult negatedResult = mock(NusmvResult.class);
        when(negatedResult.isSuccess()).thenReturn(true);
        when(negatedResult.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    lambda_r0_c0 = TRUE\n    lambda_r0_c1 = FALSE\n");

        // Forward verification passes
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

        FixSuggestionDto suggestion = strategy.tryFix(
                ctx(List.of(fault), List.of(rule), List.of(spec)));

        assertNotNull(suggestion);
        assertEquals("condition", suggestion.getStrategy());
        assertTrue(suggestion.isVerified());
        assertNotNull(suggestion.getConditionAdjustments());
        // UX-6: action="keep" entries are filtered out; only "remove" and "add" are returned
        assertEquals(1, suggestion.getConditionAdjustments().size());
        assertEquals("remove", suggestion.getConditionAdjustments().get(0).getAction());
    }

    @Test
    void tryFix_allKept_exhaustsAttemptsAndReturnsNull() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(
                        RuleDto.Condition.builder()
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

        // NuSMV keeps all conditions (lambda = TRUE for all) — strategy should retry with exclusion
        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult negatedResult = mock(NusmvResult.class);
        when(negatedResult.isSuccess()).thenReturn(true);
        when(negatedResult.getSpecResults()).thenReturn(List.of(failing));
        when(negatedResult.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    lambda_r0_c0 = TRUE\n");
        when(nusmvExecutor.execute(any(File.class))).thenReturn(negatedResult);

        // Use maxAttempts=2 to verify retry behavior without excessive looping
        FixContext context = FixContext.builder()
                .faultRules(List.of(fault))
                .allRules(List.of(rule))
                .devices(List.of())
                .specs(List.of(spec))
                .deviceSmvMap(Map.of())
                .violatedSpecIndex(0)
                .userId(1L)
                .isAttack(false)
                .intensity(0)
                .enablePrivacy(false)
                .maxAttempts(2)
                .build();

        assertNull(strategy.tryFix(context));
        // Verify it retried (2 calls = 2 attempts)
        verify(nusmvExecutor, times(2)).execute(any(File.class));
    }

    @Test
    void tryFix_nusmvFailure_exhaustsAttemptsAndReturnsNull() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(
                        RuleDto.Condition.builder()
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
                .deviceSmvMap(Map.of())
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

    @Test
    void tryFix_partialExtraction_retriesWithoutExclusion() throws Exception {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(
                        RuleDto.Condition.builder()
                                .deviceName("sensor_1").attribute("temperature").relation(">").value("30").build(),
                        RuleDto.Condition.builder()
                                .deviceName("sensor_1").attribute("humidity").relation(">").value("60").build()))
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

        // NuSMV returns counterexample with only 1 of 2 expected lambdas (partial extraction)
        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult partialResult = mock(NusmvResult.class);
        when(partialResult.isSuccess()).thenReturn(true);
        when(partialResult.getSpecResults()).thenReturn(List.of(failing));
        // Only lambda_r0_c0 extracted, lambda_r0_c1 missing → partial
        when(partialResult.getOutput()).thenReturn(
                "  -> State: 1.1 <-\n    lambda_r0_c0 = TRUE\n");
        when(nusmvExecutor.execute(any(File.class))).thenReturn(partialResult);

        FixContext context = FixContext.builder()
                .faultRules(List.of(fault))
                .allRules(List.of(rule))
                .devices(List.of())
                .specs(List.of(spec))
                .deviceSmvMap(Map.of())
                .violatedSpecIndex(0)
                .userId(1L)
                .isAttack(false)
                .intensity(0)
                .enablePrivacy(false)
                .maxAttempts(3)
                .build();

        // Should exhaust all attempts (partial extraction retries without adding exclusion)
        assertNull(strategy.tryFix(context));
        verify(nusmvExecutor, times(3)).execute(any(File.class));

        // Verify NO exclusion was added across all attempts:
        // every config passed to generateParameterized should have null exclusionInvars
        for (ParameterizationConfig captured : configCaptor.getAllValues()) {
            assertTrue(captured.getExclusionInvars() == null || captured.getExclusionInvars().isEmpty(),
                    "Partial extraction must NOT add exclusion INVARs, but found: "
                            + captured.getExclusionInvars());
        }
    }
}
