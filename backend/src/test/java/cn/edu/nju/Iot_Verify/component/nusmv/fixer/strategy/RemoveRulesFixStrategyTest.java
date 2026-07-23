package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixContext;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackPointDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
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
 * Tests for RemoveRulesFixStrategy: verifies combination search, fail-closed re-verification,
 * maxAttempts budget, and lazy DFS behavior.
 */
@ExtendWith(MockitoExtension.class)
class RemoveRulesFixStrategyTest {

    @Mock
    private SmvGenerator smvGenerator;
    @Mock
    private NusmvExecutor nusmvExecutor;

    private RemoveRulesFixStrategy strategy;

    @BeforeEach
    void setUp() {
        strategy = new RemoveRulesFixStrategy(smvGenerator, nusmvExecutor);
    }

    private SmvGenerator.GenerateResult createGenResult() throws IOException {
        File tempDir = Files.createTempDirectory("smv-test").toFile();
        File smvFile = new File(tempDir, "test.smv");
        smvFile.createNewFile();
        return new SmvGenerator.GenerateResult(smvFile, Map.of());
    }

    private FixContext ctx(List<FaultRuleDto> faultRules, List<RuleDto> allRules, int maxAttempts) {
        return ctx(faultRules, allRules, maxAttempts, AttackScenarioDto.none());
    }

    private FixContext ctx(List<FaultRuleDto> faultRules, List<RuleDto> allRules, int maxAttempts,
                           AttackScenarioDto attackScenario) {
        return FixContext.builder()
                .faultRules(faultRules)
                .allRules(allRules)
                .devices(List.of())
                .environmentVariables(List.of())
                .specs(List.of())
                .deviceSmvMap(Map.of())
                .violatedSpecIndex(0)
                .userId(1L)
                .attackScenario(attackScenario)
                .enablePrivacy(false)
                .maxAttempts(maxAttempts)
                .build();
    }

    private void mockGenerateReturns(SmvGenerator.GenerateResult genResult) throws IOException {
        when(smvGenerator.generateWithResolvedDeviceModel(
                anyLong(), anyList(), anyList(), anyList(), anyList(),
                any(), anyBoolean(),
                any(SmvGenerator.GeneratePurpose.class),
                any(SmvGenerator.TempModelContext.class), anyMap()))
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
        assertEquals("remove", suggestion.getStrategy());
        assertTrue(suggestion.isVerified());
        assertEquals(List.of(1), suggestion.getRemovedRuleIndices());
        assertEquals(List.of("rule1 (fault)"), suggestion.getRemovedRuleDescriptions());
        assertFalse(suggestion.getDescription().contains("'rule1 (fault)'"));
    }

    @Test
    void tryFix_expandsToDormantSpecRelatedRuleAndFindsPairRemoval() throws Exception {
        mockGenerateReturns(createGenResult());

        SpecCheckResult failing = mock(SpecCheckResult.class);
        when(failing.isPassed()).thenReturn(false);
        NusmvResult failedVerification = mock(NusmvResult.class);
        when(failedVerification.isSuccess()).thenReturn(true);
        when(failedVerification.getSpecResults()).thenReturn(List.of(failing));
        SpecCheckResult passing = mock(SpecCheckResult.class);
        when(passing.isPassed()).thenReturn(true);
        NusmvResult passedVerification = mock(NusmvResult.class);
        when(passedVerification.isSuccess()).thenReturn(true);
        when(passedVerification.getSpecResults()).thenReturn(List.of(passing));
        when(nusmvExecutor.execute(any(File.class)))
                .thenReturn(failedVerification, failedVerification, passedVerification);

        DeviceSmvData sensor = new DeviceSmvData();
        sensor.setVarName("sensor_1");
        DeviceSmvData heater = new DeviceSmvData();
        heater.setVarName("heater_1");
        List<RuleDto> allRules = List.of(
                RuleDto.builder().ruleString("executed unsafe rule")
                        .conditions(List.of(RuleDto.Condition.builder()
                                .deviceName("sensor_1").attribute("temperature")
                                .targetType("variable").relation(">=").value("28").build()))
                        .command(RuleDto.Command.builder()
                                .deviceName("heater_1").action("heat").build())
                        .build(),
                RuleDto.builder().ruleString("dormant backup rule")
                        .conditions(List.of(RuleDto.Condition.builder()
                                .deviceName("sensor_1").attribute("temperature")
                                .targetType("variable").relation(">=").value("29").build()))
                        .command(RuleDto.Command.builder()
                                .deviceName("heater_1").action("heat").build())
                        .build());
        SpecConditionDto condition = new SpecConditionDto();
        condition.setDeviceId("heater_1");
        condition.setTargetType("mode");
        condition.setKey("Mode");
        condition.setRelation("=");
        condition.setValue("heat");
        SpecificationDto spec = new SpecificationDto();
        spec.setId("safety");
        spec.setTemplateId("3");
        spec.setAConditions(List.of(condition));
        spec.setIfConditions(List.of());
        spec.setThenConditions(List.of());
        FixContext context = FixContext.builder()
                .faultRules(List.of(FaultRuleDto.builder().ruleIndex(0).build()))
                .allRules(allRules)
                .devices(List.of())
                .environmentVariables(List.of())
                .specs(List.of(spec))
                .deviceSmvMap(Map.of("sensor_1", sensor, "heater_1", heater))
                .violatedSpecIndex(0)
                .userId(1L)
                .attackScenario(AttackScenarioDto.none())
                .maxAttempts(3)
                .build();

        FixSuggestionDto suggestion = strategy.tryFix(context);

        assertNotNull(suggestion);
        assertEquals(List.of(0, 1), suggestion.getRemovedRuleIndices());
        verify(nusmvExecutor, times(3)).execute(any(File.class));
    }

    @Test
    void tryFix_rejectsRemovalOfExplicitlyAttackedAutomationLink() {
        List<FaultRuleDto> faultRules = List.of(FaultRuleDto.builder().ruleIndex(0).build());
        List<RuleDto> allRules = List.of(
                RuleDto.builder().id(7L).ruleString("selected attacked link").build());
        FixContext context = ctx(faultRules, allRules, 20,
                AttackScenarioDto.exactPoints(List.of(AttackPointDto.automationLink(7L))));

        FixSuggestionDto suggestion = strategy.tryFix(context);

        assertNull(suggestion);
        verifyNoInteractions(smvGenerator, nusmvExecutor);
        assertTrue(context.diagnosticsSnapshot().stream()
                .anyMatch(message -> message.contains("selected automation-link attack point")));
    }

    @Test
    void tryFix_rejectsRemovalThatEliminatesExplicitDeviceAttackPoint() {
        DeviceSmvData light = new DeviceSmvData();
        light.setVarName("light_1");
        List<FaultRuleDto> faultRules = List.of(FaultRuleDto.builder().ruleIndex(0).build());
        List<RuleDto> allRules = List.of(RuleDto.builder()
                .id(7L)
                .ruleString("selected attacked actuator")
                .command(RuleDto.Command.builder().deviceName("light_1").action("on").build())
                .build());
        FixContext context = FixContext.builder()
                .faultRules(faultRules)
                .allRules(allRules)
                .devices(List.of())
                .environmentVariables(List.of())
                .specs(List.of())
                .deviceSmvMap(Map.of("light_1", light))
                .violatedSpecIndex(0)
                .userId(1L)
                .attackScenario(AttackScenarioDto.exactPoints(List.of(
                        AttackPointDto.device("light_1"))))
                .maxAttempts(20)
                .build();

        FixSuggestionDto suggestion = strategy.tryFix(context);

        assertNull(suggestion);
        verifyNoInteractions(smvGenerator, nusmvExecutor);
        assertTrue(context.diagnosticsSnapshot().stream()
                .anyMatch(message -> message.contains("device attack point")));
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
    void tryFix_rejectsCandidateWhenForwardModelDisabledAnyRule() throws Exception {
        SmvGenerator.GenerateResult incomplete = createGenResult();
        incomplete = new SmvGenerator.GenerateResult(
                incomplete.smvFile(), Map.of(),
                List.of("Generation warning [rule-disabled]: invalid rule"), 1, 0, List.of());
        mockGenerateReturns(incomplete);

        List<FaultRuleDto> faultRules = List.of(FaultRuleDto.builder().ruleIndex(0).build());
        List<RuleDto> allRules = List.of(RuleDto.builder().ruleString("rule0").build());
        FixContext context = ctx(faultRules, allRules, 20);

        FixSuggestionDto suggestion = strategy.tryFix(context);

        assertNull(suggestion);
        verify(nusmvExecutor, never()).execute(any(File.class));
        assertTrue(context.diagnosticsSnapshot().stream().anyMatch(message -> message.contains("incomplete model")));
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
                RuleDto.builder().command(RuleDto.Command.builder().deviceName("d0").action("a").build()).build(),
                RuleDto.builder().command(RuleDto.Command.builder().deviceName("d1").action("a").build()).build(),
                RuleDto.builder().command(RuleDto.Command.builder().deviceName("d2").action("a").build()).build(),
                RuleDto.builder().command(RuleDto.Command.builder().deviceName("d3").action("a").build()).build(),
                RuleDto.builder().command(RuleDto.Command.builder().deviceName("d4").action("a").build()).build());

        FixContext context = ctx(faultRules, allRules, 3);
        FixSuggestionDto suggestion = strategy.tryFix(context);

        assertNull(suggestion);
        verify(nusmvExecutor, atMost(3)).execute(any(File.class));
        assertEquals(3, context.strategySearchProgress("remove").attemptsUsed());
        assertEquals("SEARCH_BUDGET_EXHAUSTED", context.strategyNoResult("remove").status());
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
        FixContext context = ctx(faultRules, allRules, 0);
        strategy.tryFix(context);

        // Should still execute (defaulted to 20, but only 1 combination exists)
        verify(nusmvExecutor, times(1)).execute(any(File.class));
        assertNull(context.strategyNoResult("remove"),
                "checking the complete one-candidate space is not budget exhaustion");
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

        FixContext context = ctx(faultRules, allRules, 20);
        FixSuggestionDto suggestion = strategy.tryFix(context);

        assertNull(suggestion);
        assertNotNull(context.strategySolverFailure("remove"));
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
