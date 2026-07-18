package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.AttackSurface;
import cn.edu.nju.Iot_Verify.dto.model.AttackPointDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import cn.edu.nju.Iot_Verify.util.DeviceNameNormalizer;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.HashMap;
import java.util.Map;
import java.util.List;
import java.util.Set;

/** Conditional validation and canonicalization for per-run attack scenarios. */
final class AttackScenarioValidator {

    private static final int MAX_ATTACK_POINTS = 50;

    private AttackScenarioValidator() {
    }

    static AttackScenarioDto canonicalizeForVerification(AttackScenarioDto scenario) {
        return canonicalize(scenario, true);
    }

    static AttackScenarioDto canonicalizeForSimulation(AttackScenarioDto scenario) {
        return canonicalize(scenario, false);
    }

    static void validateAgainstSurface(AttackScenarioDto scenario,
                                       AttackSurface surface,
                                       List<RuleDto> rules) {
        AttackScenarioDto safeScenario = scenario != null ? scenario : AttackScenarioDto.none();
        AttackSurface safeSurface = surface != null ? surface : new AttackSurface(Set.of(), 0, 0);

        if (safeScenario.getMode() == AttackScenarioDto.Mode.NONE) {
            return;
        }
        if (safeSurface.totalCount() < 1) {
            throw new ValidationException("attackScenario",
                    "Attack modeling would not change this model because it has no behavior-changing attack points");
        }
        if (safeScenario.getMode() == AttackScenarioDto.Mode.ANY_UP_TO_BUDGET) {
            if (safeScenario.effectiveBudget() > safeSurface.totalCount()) {
                throw new ValidationException("attackScenario.budget",
                        "Attack budget cannot exceed the behavior-changing device and automation-link points ("
                                + safeSurface.totalCount() + ")");
            }
            return;
        }

        Map<Long, Integer> ruleIdCounts = new HashMap<>();
        if (rules != null) {
            for (RuleDto rule : rules) {
                if (rule != null && rule.getId() != null) {
                    ruleIdCounts.merge(rule.getId(), 1, Integer::sum);
                }
            }
        }
        List<AttackPointDto> points = safeScenario.getPoints() != null
                ? safeScenario.getPoints() : List.of();
        for (int index = 0; index < points.size(); index++) {
            AttackPointDto point = points.get(index);
            if (point.getKind() == AttackPointDto.Kind.DEVICE
                    && !safeSurface.includesDevice(point.getDeviceId())) {
                throw new ValidationException("attackScenario.points[" + index + "].deviceId",
                        "Selected device is not a behavior-changing attack point in this run");
            }
            if (point.getKind() == AttackPointDto.Kind.AUTOMATION_LINK
                    && ruleIdCounts.getOrDefault(point.getRuleId(), 0) != 1) {
                throw new ValidationException("attackScenario.points[" + index + "].ruleId",
                        "Selected automation link must reference exactly one submitted persisted rule");
            }
        }
    }

    private static AttackScenarioDto canonicalize(AttackScenarioDto scenario,
                                                   boolean allowExhaustiveSelection) {
        AttackScenarioDto safeScenario = scenario != null ? scenario : AttackScenarioDto.none();
        AttackScenarioDto.Mode mode = safeScenario.getMode();
        if (mode == null) {
            throw new ValidationException("attackScenario.mode", "Attack scenario mode is required");
        }
        List<AttackPointDto> points = safeScenario.getPoints() == null
                ? List.of() : safeScenario.getPoints();
        Integer budget = safeScenario.getBudget();

        if (mode == AttackScenarioDto.Mode.NONE) {
            if (budget != null && budget != 0) {
                throw new ValidationException("attackScenario.budget",
                        "Attack budget must be omitted or 0 when no attack scenario is selected");
            }
            if (!points.isEmpty()) {
                throw new ValidationException("attackScenario.points",
                        "Attack points must be empty when no attack scenario is selected");
            }
            return AttackScenarioDto.none();
        }

        if (mode == AttackScenarioDto.Mode.ANY_UP_TO_BUDGET) {
            if (!allowExhaustiveSelection) {
                throw new ValidationException("attackScenario.mode",
                        "Simulation requires explicit attack points; budget-based exhaustive selection is verification-only");
            }
            if (budget == null || budget < 1 || budget > MAX_ATTACK_POINTS) {
                throw new ValidationException("attackScenario.budget",
                        "Attack budget must be between 1 and 50 for exhaustive verification");
            }
            if (!points.isEmpty()) {
                throw new ValidationException("attackScenario.points",
                        "Explicit attack points cannot be combined with exhaustive budget selection");
            }
            return AttackScenarioDto.anyUpToBudget(budget);
        }

        if (budget != null && budget != 0) {
            throw new ValidationException("attackScenario.budget",
                    "Exact attack scenarios derive their size from points and must omit budget");
        }
        if (points.isEmpty()) {
            throw new ValidationException("attackScenario.points",
                    "At least one explicit attack point is required");
        }
        if (points.size() > MAX_ATTACK_POINTS) {
            throw new ValidationException("attackScenario.points",
                    "At most 50 explicit attack points may be selected");
        }

        List<AttackPointDto> canonicalPoints = new ArrayList<>();
        Set<String> identities = new HashSet<>();
        for (int index = 0; index < points.size(); index++) {
            AttackPointDto point = points.get(index);
            if (point == null || point.getKind() == null) {
                throw new ValidationException("attackScenario.points[" + index + "].kind",
                        "Attack point kind is required");
            }
            AttackPointDto canonicalPoint;
            if (point.getKind() == AttackPointDto.Kind.DEVICE) {
                String deviceId = trimToNull(point.getDeviceId());
                if (deviceId == null) {
                    throw new ValidationException("attackScenario.points[" + index + "].deviceId",
                            "Device attack points require deviceId");
                }
                if (!deviceId.equals(DeviceNameNormalizer.normalize(deviceId))) {
                    throw new ValidationException("attackScenario.points[" + index + "].deviceId",
                            "Device attack point id must be the NuSMV-safe normalized node id");
                }
                if (point.getRuleId() != null) {
                    throw new ValidationException("attackScenario.points[" + index + "].ruleId",
                            "Device attack points must omit ruleId");
                }
                canonicalPoint = AttackPointDto.device(deviceId);
            } else {
                if (point.getRuleId() == null || point.getRuleId() < 1) {
                    throw new ValidationException("attackScenario.points[" + index + "].ruleId",
                            "Automation-link attack points require a positive persisted ruleId");
                }
                if (trimToNull(point.getDeviceId()) != null) {
                    throw new ValidationException("attackScenario.points[" + index + "].deviceId",
                            "Automation-link attack points must omit deviceId");
                }
                canonicalPoint = AttackPointDto.automationLink(point.getRuleId());
            }
            if (!identities.add(canonicalPoint.identityKey())) {
                throw new ValidationException("attackScenario.points[" + index + "]",
                        "Duplicate attack point: " + canonicalPoint.identityKey());
            }
            canonicalPoints.add(canonicalPoint);
        }
        canonicalPoints.sort(Comparator.comparing(AttackPointDto::identityKey));
        return AttackScenarioDto.exactPoints(canonicalPoints);
    }

    private static String trimToNull(String value) {
        if (value == null) {
            return null;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }
}
