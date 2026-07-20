package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.dto.model.AttackPointDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/** Shared domain validation for exact attack selections against a generated-model surface. */
public final class AttackScenarioSurfaceValidator {

    private AttackScenarioSurfaceValidator() {
    }

    public static Optional<Violation> firstExactSelectionViolation(
            AttackScenarioDto scenario,
            AttackSurface surface,
            List<RuleDto> rules) {
        if (scenario == null || scenario.getMode() != AttackScenarioDto.Mode.EXACT_POINTS) {
            return Optional.empty();
        }

        AttackSurface safeSurface = surface != null
                ? surface
                : new AttackSurface(java.util.Set.of(), 0, 0);
        Map<Long, Integer> ruleIdCounts = new HashMap<>();
        if (rules != null) {
            for (RuleDto rule : rules) {
                if (rule != null && rule.getId() != null) {
                    ruleIdCounts.merge(rule.getId(), 1, Integer::sum);
                }
            }
        }

        List<AttackPointDto> points = scenario.getPoints() != null
                ? scenario.getPoints()
                : List.of();
        for (int index = 0; index < points.size(); index++) {
            AttackPointDto point = points.get(index);
            if (point == null || point.getKind() == null) {
                return Optional.of(new Violation(index, "kind", "Attack point kind is required"));
            }
            if (point.getKind() == AttackPointDto.Kind.DEVICE
                    && !safeSurface.includesDevice(point.getDeviceId())) {
                return Optional.of(new Violation(index, "deviceId",
                        "Selected device is not a behavior-changing attack point in this run"));
            }
            if (point.getKind() == AttackPointDto.Kind.AUTOMATION_LINK
                    && ruleIdCounts.getOrDefault(point.getRuleId(), 0) != 1) {
                return Optional.of(new Violation(index, "ruleId",
                        "Selected automation link must reference exactly one submitted persisted rule"));
            }
        }
        return Optional.empty();
    }

    public record Violation(int pointIndex, String field, String message) {
    }
}
