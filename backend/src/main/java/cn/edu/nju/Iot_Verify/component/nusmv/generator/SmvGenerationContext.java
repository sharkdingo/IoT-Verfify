package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;

import java.util.List;

/**
 * Per-generation context passed through the SMV builder chain.
 *
 * <p>The context is request-scoped and contains no static mutable state, so concurrent
 * verification/simulation requests cannot share warning state accidentally.</p>
 */
public final class SmvGenerationContext {

    private final SmvGenerationWarningCollector warnings;

    private SmvGenerationContext(SmvGenerationWarningCollector warnings) {
        this.warnings = warnings;
    }

    public static SmvGenerationContext collecting() {
        return new SmvGenerationContext(new SmvGenerationWarningCollector());
    }

    public static SmvGenerationContext noop() {
        return new SmvGenerationContext(null);
    }

    public void disabledRule(RuleDto rule, String reason) {
        if (warnings != null) {
            warnings.disabledRule(rule, reason);
        }
    }

    public void skippedSpec(SpecificationDto spec, String reason) {
        if (warnings != null) {
            warnings.skippedSpec(spec, reason);
        }
    }

    public void emittedSpec(SpecificationDto spec, String expression) {
        if (warnings != null) {
            warnings.emittedSpec(spec, expression);
        }
    }

    public WarningSnapshot warningsSnapshot() {
        if (warnings == null) {
            return WarningSnapshot.empty();
        }
        return new WarningSnapshot(
                warnings.checkLogWarnings(),
                warnings.disabledRuleCount(),
                warnings.skippedSpecCount(),
                warnings.emittedSpecs()
        );
    }

    public record WarningSnapshot(List<String> checkLogWarnings,
                                  int disabledRuleCount,
                                  int skippedSpecCount,
                                  List<EmittedSpec> emittedSpecs) {
        public static WarningSnapshot empty() {
            return new WarningSnapshot(List.of(), 0, 0, List.of());
        }
    }

    public record EmittedSpec(SpecificationDto spec, String specId, String expression) {
    }
}
