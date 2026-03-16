package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixContext;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
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

/**
 * Tests for DisableFixStrategy: verifies combination search, fail-closed re-verification,
 * maxAttempts budget, and lazy DFS behavior.
 */
@ExtendWith(MockitoExtension.class)
class DisableFixStrategyTest {

    @Mock
    private SmvGenerator smvGenerator;
    @Mock
    private NusmvExecutor nusmvExecutor;

    private DisableFixStrategy strategy;

    @BeforeEach
    void setUp() {
        strategy = new DisableFixStrategy(smvGenerator, nusmvExecutor);
    }

    private SmvGenerator.GenerateResult createGenResult() throws IOException {
        File tempDir = Files.createTempDirectory("smv-test").toFile();
        File smvFile = new File(tempDir, "test.smv");
        smvFile.createNewFile();
        return new SmvGenerator.GenerateResult(smvFile, Map.of());
    }

    private FixContext ctx(List<FaultRuleDto> faultRules, List<RuleDto> allRules, int maxAttempts) {
        return FixContext.builder()
                .faultRules(faultRules)
                .allRules(allRules)
                .devices(List.of())
                .specs(List.of())
                .deviceSmvMap(Map.of())
                .violatedSpecIndex(0)
                .userId(1L)
                .isAttack(false)
                .intensity(0)
                .enablePrivacy(false)
                .maxAttempts(maxAttempts)
                .build();
    }

    private void mockGenerateReturns(SmvGenerator.GenerateResult genResult) throws IOException {
        when(smvGenerator.generate(anyLong(), anyList(), anyList(), anyList(),
                anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(genResult);
    }

    @Test
    void tryFix_nullFaultRules_returnsNull() {
        assertNull(strategy.tryFix(ctx(null, List.of(), 20)));
    }

    @Test
    void tryFix_emptyFaultRules_returnsNull() {
        assertNull(strategy.tryFix(ctx(List.of(), List.of(), 20)));
    }

    @Test
    void tryFix_singleFaultRule_disableFixesViolation() throws Exception {
        mockGenerateReturns(createGenResult());

        SpecCheckResult passing = mock(SpecCheckResult.class);
        when(passing.isPassed()).thenReturn(true);
        NusmvResult nusmvResult = mock(NusmvResult.class);
        when(nusmvResult.isSuccess()).thenReturn(true);
        when(nusmvResult.getSpecResults()).thenReturn(List.of(passing));
        when(nusmvExecutor.execute(any(File.class))).thenReturn(nusmvResult);

        List<FaultRuleDto> faultRules = List.of(
                FaultRuleDto.builder().ruleIndex(1).build());
        List<RuleDto> allRules = List.of(
                RuleDto.builder().ruleString("rule0").build(),
                RuleDto.builder().ruleString("rule1 (fault)").build());

        FixSuggestionDto suggestion = strategy.tryFix(ctx(faultRules, allRules, 20));

        assertNotNull(suggestion);
        assertEquals("disable", suggestion.getStrategy());
        assertTrue(suggestion.isVerified());
        assertEquals(List.of(1), suggestion.getDisabledRuleIndices());
    }

    @Test
    void tryFix_failClosedOnEmptySpecResults() throws Exception {
        mockGenerateReturns(createGenResult());

        NusmvResult nusmvResult = mock(NusmvResult.class);
        when(nusmvResult.isSuccess()).thenReturn(true);
        when(nusmvResult.getSpecResults()).thenReturn(List.of()); // empty!
        when(nusmvExecutor.execute(any(File.class))).thenReturn(nusmvResult);

        List<FaultRuleDto> faultRules = List.of(FaultRuleDto.builder().ruleIndex(0).build());
        List<RuleDto> allRules = List.of(RuleDto.builder().ruleString("rule0").build());

        FixSuggestionDto suggestion = strategy.tryFix(ctx(faultRules, allRules, 20));

        // Should return null because empty specResults → fail-closed → no fix confirmed
        assertNull(suggestion);
    }

    @Test
    void tryFix_respectsMaxAttemptsBudget() throws Exception {
        mockGenerateReturns(createGenResult());

        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult nusmvResult = mock(NusmvResult.class);
        when(nusmvResult.isSuccess()).thenReturn(true);
        when(nusmvResult.getSpecResults()).thenReturn(List.of(failing));
        when(nusmvExecutor.execute(any(File.class))).thenReturn(nusmvResult);

        // 5 fault rules → many possible combinations, but maxAttempts=3 should cap it
        List<FaultRuleDto> faultRules = List.of(
                FaultRuleDto.builder().ruleIndex(0).build(),
                FaultRuleDto.builder().ruleIndex(1).build(),
                FaultRuleDto.builder().ruleIndex(2).build(),
                FaultRuleDto.builder().ruleIndex(3).build(),
                FaultRuleDto.builder().ruleIndex(4).build());
        List<RuleDto> allRules = List.of(
                RuleDto.builder().build(), RuleDto.builder().build(),
                RuleDto.builder().build(), RuleDto.builder().build(),
                RuleDto.builder().build());

        FixSuggestionDto suggestion = strategy.tryFix(ctx(faultRules, allRules, 3));

        assertNull(suggestion);
        verify(nusmvExecutor, atMost(3)).execute(any(File.class));
    }

    @Test
    void tryFix_invalidMaxAttemptsDefaultsTo20() throws Exception {
        mockGenerateReturns(createGenResult());

        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult nusmvResult = mock(NusmvResult.class);
        when(nusmvResult.isSuccess()).thenReturn(true);
        when(nusmvResult.getSpecResults()).thenReturn(List.of(failing));
        when(nusmvExecutor.execute(any(File.class))).thenReturn(nusmvResult);

        List<FaultRuleDto> faultRules = List.of(FaultRuleDto.builder().ruleIndex(0).build());
        List<RuleDto> allRules = List.of(RuleDto.builder().build());

        // maxAttempts=0 should be corrected to 20
        strategy.tryFix(ctx(faultRules, allRules, 0));

        // Should still execute (defaulted to 20, but only 1 combination exists)
        verify(nusmvExecutor, times(1)).execute(any(File.class));
    }

    @Test
    void tryFix_nusmvExecutionFailure_treatedAsNoFix() throws Exception {
        mockGenerateReturns(createGenResult());

        NusmvResult failedResult = mock(NusmvResult.class);
        when(failedResult.isSuccess()).thenReturn(false);
        when(failedResult.getErrorMessage()).thenReturn("NuSMV crashed");
        when(nusmvExecutor.execute(any(File.class))).thenReturn(failedResult);

        List<FaultRuleDto> faultRules = List.of(FaultRuleDto.builder().ruleIndex(0).build());
        List<RuleDto> allRules = List.of(RuleDto.builder().build());

        FixSuggestionDto suggestion = strategy.tryFix(ctx(faultRules, allRules, 20));

        assertNull(suggestion);
    }

    @Test
    void tryFix_smvGeneratorReturnsNull_treatedAsNoFix() throws Exception {
        mockGenerateReturns(null);

        List<FaultRuleDto> faultRules = List.of(FaultRuleDto.builder().ruleIndex(0).build());
        List<RuleDto> allRules = List.of(RuleDto.builder().build());

        FixSuggestionDto suggestion = strategy.tryFix(ctx(faultRules, allRules, 20));

        assertNull(suggestion);
    }
}
