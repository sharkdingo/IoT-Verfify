package cn.edu.nju.Iot_Verify.component.nusmv.fixer;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.localize.FaultLocalizer;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

/**
 * Tests for RuleFixer default strategy chain behavior (P0 regression).
 */
@ExtendWith(MockitoExtension.class)
class RuleFixerTest {

    @Mock private FaultLocalizer faultLocalizer;

    private FixConfig fixConfig() {
        FixConfig cfg = new FixConfig();
        cfg.setFixTimeoutMs(300_000);
        return cfg;
    }

    private FixStrategy mockStrategy(String name, boolean requiresSpec) {
        FixStrategy s = mock(FixStrategy.class);
        when(s.name()).thenReturn(name);
        lenient().when(s.requiresViolatedSpec()).thenReturn(requiresSpec);
        return s;
    }

    /**
     * When strategies=null, RuleFixer should use DEFAULT_STRATEGIES and try all three.
     * Precondition: valid violatedSpecId (index >= 0) and non-empty faultRules,
     * otherwise requiresViolatedSpec strategies get skipped.
     */
    @Test
    void fix_nullStrategies_usesDefaultAndTriesAllThree() {
        FixStrategy paramStrategy = mockStrategy("parameter", true);
        FixStrategy condStrategy = mockStrategy("condition", true);
        FixStrategy disableStrategy = mockStrategy("disable", false);

        RuleFixer fixer = new RuleFixer(faultLocalizer,
                List.of(paramStrategy, condStrategy, disableStrategy), fixConfig());

        // Setup: faultLocalizer returns non-empty fault rules
        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        when(faultLocalizer.localize(any(), any(), any())).thenReturn(List.of(fault));

        // Setup: spec with id matching violatedSpecId
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_0");

        RuleDto rule = RuleDto.builder().build();

        fixer.fix(1L, "spec_0", List.of(), List.of(rule), List.of(), List.of(spec),
                Map.of(), 1L, false, 0, false, null, 20, null);

        // All three strategies should have tryFix called
        verify(paramStrategy).tryFix(any(FixContext.class));
        verify(condStrategy).tryFix(any(FixContext.class));
        verify(disableStrategy).tryFix(any(FixContext.class));
    }

    @Test
    void fix_emptyStrategies_usesDefaultChain() {
        FixStrategy paramStrategy = mockStrategy("parameter", true);
        FixStrategy condStrategy = mockStrategy("condition", true);
        FixStrategy disableStrategy = mockStrategy("disable", false);

        RuleFixer fixer = new RuleFixer(faultLocalizer,
                List.of(paramStrategy, condStrategy, disableStrategy), fixConfig());

        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        when(faultLocalizer.localize(any(), any(), any())).thenReturn(List.of(fault));

        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_0");
        RuleDto rule = RuleDto.builder().build();

        // Pass empty list — should fall back to DEFAULT_STRATEGIES
        fixer.fix(1L, "spec_0", List.of(), List.of(rule), List.of(), List.of(spec),
                Map.of(), 1L, false, 0, false, List.of(), 20, null);

        verify(paramStrategy).tryFix(any(FixContext.class));
        verify(condStrategy).tryFix(any(FixContext.class));
        verify(disableStrategy).tryFix(any(FixContext.class));
    }

    @Test
    void fix_explicitDisableOnly_onlyDisableCalled() {
        FixStrategy paramStrategy = mockStrategy("parameter", true);
        FixStrategy condStrategy = mockStrategy("condition", true);
        FixStrategy disableStrategy = mockStrategy("disable", false);

        RuleFixer fixer = new RuleFixer(faultLocalizer,
                List.of(paramStrategy, condStrategy, disableStrategy), fixConfig());

        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        when(faultLocalizer.localize(any(), any(), any())).thenReturn(List.of(fault));

        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_0");
        RuleDto rule = RuleDto.builder().build();

        fixer.fix(1L, "spec_0", List.of(), List.of(rule), List.of(), List.of(spec),
                Map.of(), 1L, false, 0, false, List.of("disable"), 20, null);

        verify(paramStrategy, never()).tryFix(any());
        verify(condStrategy, never()).tryFix(any());
        verify(disableStrategy).tryFix(any(FixContext.class));
    }

    @Test
    void fix_expiredDeadline_skipsAllStrategiesAndAppendsSummary() {
        FixStrategy paramStrategy = mockStrategy("parameter", true);
        FixStrategy condStrategy = mockStrategy("condition", true);
        FixStrategy disableStrategy = mockStrategy("disable", false);

        // Use a fixConfig with 1000ms (minimum allowed), but we don't rely on it expiring —
        // the faultLocalizer mock will return instantly, so the deadline won't expire naturally.
        // Instead we test the summary text by using a very short timeout.
        // A more reliable approach: we verify that the summary contains "timed out"
        // when the deadline is already expired by the time strategies run.
        // To simulate this, we use a fixConfig with minimum timeout and a slow strategy.
        FixConfig expiredConfig = new FixConfig();
        expiredConfig.setFixTimeoutMs(1000); // minimum allowed

        RuleFixer fixer = new RuleFixer(faultLocalizer,
                List.of(paramStrategy, condStrategy, disableStrategy), expiredConfig);

        FaultRuleDto fault = FaultRuleDto.builder().ruleIndex(0).build();
        when(faultLocalizer.localize(any(), any(), any())).thenReturn(List.of(fault));

        // Make first strategy consume the deadline
        when(paramStrategy.tryFix(any())).thenAnswer(inv -> {
            Thread.sleep(1100); // exceed 1000ms deadline
            return null;
        });

        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_0");
        RuleDto rule = RuleDto.builder().build();

        FixResultDto result = fixer.fix(1L, "spec_0", List.of(), List.of(rule), List.of(), List.of(spec),
                Map.of(), 1L, false, 0, false, null, 20, null);

        // After paramStrategy sleeps past deadline, remaining strategies should be skipped
        verify(paramStrategy).tryFix(any(FixContext.class));
        verify(condStrategy, never()).tryFix(any());
        verify(disableStrategy, never()).tryFix(any());
        assertTrue(result.getSummary().contains("timed out"));
    }
}
