package cn.edu.nju.Iot_Verify.dto.model;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.AttackSurface;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;
import java.util.ArrayList;
import java.util.Map;

/** Machine-readable assumptions that define what one verification/simulation run modeled. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class ModelSemanticsDto {

    public enum AttackPointUnit {
        BEHAVIOR_CHANGING_DEVICE_INSTANCE_OR_AUTOMATION_LINK
    }

    public enum AttackEffect {
        DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN,
        COMMAND_TO_COMPROMISED_TARGET_IS_DROPPED,
        COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED
    }

    public enum AttackSelectionPolicy {
        NOT_MODELED,
        EXACT_ATTACK_POINTS,
        UP_TO_ATTACK_BUDGET_NONDETERMINISTIC
    }

    public enum TrustPropagationPolicy {
        TARGET_UNTRUSTED_IF_ALL_TRIGGER_SOURCES_UNTRUSTED
    }

    public enum PrivacyPropagationPolicy {
        TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE,
        NOT_MODELED
    }

    public enum LabelPropagationScope {
        AUTOMATION_RULE_COMMANDS_ONLY
    }

    public enum EnvironmentEvolutionEffect {
        DECLARED_NUMERIC_RATES_AND_DEVICE_EFFECTS_WITHIN_DOMAIN,
        DISCRETE_VALUES_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN
    }

    public enum LocalVariableFallbackPolicy {
        STUTTER_WHEN_NO_DECLARED_EVOLUTION
    }

    private AttackPointUnit attackPointUnit;
    private AttackSelectionPolicy attackSelectionPolicy;
    private List<SelectedAttackPointDto> selectedAttackPoints;
    private List<AttackEffect> attackEffects;
    private int modeledDeviceAttackPointCount;
    private int modeledFalsifiableReadingDeviceCount;
    private int modeledAutomationLinkAttackPointCount;
    private int modeledAttackPointCount;
    private TrustPropagationPolicy trustPropagationPolicy;
    private PrivacyPropagationPolicy privacyPropagationPolicy;
    private LabelPropagationScope labelPropagationScope;
    private List<EnvironmentEvolutionEffect> environmentEvolutionEffects;
    private LocalVariableFallbackPolicy localVariableFallbackPolicy;

    public static ModelSemanticsDto forRun(boolean isAttack,
                                           boolean enablePrivacy,
                                           int deviceCount,
                                           int automationLinkCount,
                                           int falsifiableReadingDeviceCount) {
        return forRun(isAttack ? AttackScenarioDto.anyUpToBudget(1) : AttackScenarioDto.none(),
                enablePrivacy, deviceCount, automationLinkCount, falsifiableReadingDeviceCount);
    }

    public static ModelSemanticsDto forRun(AttackScenarioDto attackScenario,
                                           boolean enablePrivacy,
                                           AttackSurface attackSurface) {
        AttackSurface safeSurface = attackSurface != null
                ? attackSurface : new AttackSurface(java.util.Set.of(), 0, 0);
        AttackScenarioDto safeScenario = attackScenario != null ? attackScenario : AttackScenarioDto.none();
        boolean falsifiableEffect = safeScenario.getMode() == AttackScenarioDto.Mode.ANY_UP_TO_BUDGET
                ? safeSurface.hasFalsifiableReadingEffect()
                : safeScenario.selectedDeviceIds().stream()
                        .anyMatch(safeSurface::includesFalsifiableReadingDevice);
        boolean commandTargetDropEffect = safeScenario.getMode() == AttackScenarioDto.Mode.ANY_UP_TO_BUDGET
                ? !safeSurface.commandTargetDeviceVarNames().isEmpty()
                : safeScenario.selectedDeviceIds().stream()
                        .anyMatch(safeSurface::includesCommandTargetDevice);
        return buildForRun(safeScenario, enablePrivacy, safeSurface.deviceCount(),
                safeSurface.automationLinkCount(), safeSurface.falsifiableReadingDeviceCount(),
                falsifiableEffect, commandTargetDropEffect,
                safeSurface.deviceDisplayLabels(), safeSurface.automationLinkDisplayLabels());
    }

    public static ModelSemanticsDto forRun(AttackScenarioDto attackScenario,
                                           boolean enablePrivacy,
                                           int deviceCount,
                                           int automationLinkCount,
                                           int falsifiableReadingDeviceCount) {
        AttackScenarioDto safeScenario = attackScenario != null ? attackScenario : AttackScenarioDto.none();
        boolean falsifiableEffect = safeScenario.getMode() == AttackScenarioDto.Mode.ANY_UP_TO_BUDGET
                ? falsifiableReadingDeviceCount > 0
                : !safeScenario.selectedDeviceIds().isEmpty() && falsifiableReadingDeviceCount > 0;
        boolean commandTargetDropEffect = safeScenario.getMode() == AttackScenarioDto.Mode.ANY_UP_TO_BUDGET
                ? deviceCount > 0 && automationLinkCount > 0
                : !safeScenario.selectedDeviceIds().isEmpty() && automationLinkCount > 0;
        return buildForRun(safeScenario, enablePrivacy, deviceCount, automationLinkCount,
                falsifiableReadingDeviceCount, falsifiableEffect, commandTargetDropEffect,
                Map.of(), Map.of());
    }

    private static ModelSemanticsDto buildForRun(AttackScenarioDto attackScenario,
                                                 boolean enablePrivacy,
                                                 int deviceCount,
                                                 int automationLinkCount,
                                                 int falsifiableReadingDeviceCount,
                                                 boolean falsifiableEffect,
                                                 boolean commandTargetDropEffect,
                                                 Map<String, String> deviceDisplayLabels,
                                                 Map<Long, String> automationLinkDisplayLabels) {
        int safeDeviceCount = Math.max(0, deviceCount);
        int safeAutomationLinkCount = Math.max(0, automationLinkCount);
        int safeFalsifiableReadingDeviceCount = Math.max(0,
                Math.min(falsifiableReadingDeviceCount, safeDeviceCount));
        boolean isAttack = attackScenario.isEnabled();
        boolean hasSelectedLink = attackScenario.getMode() == AttackScenarioDto.Mode.ANY_UP_TO_BUDGET
                ? safeAutomationLinkCount > 0 : !attackScenario.selectedAutomationLinkRuleIds().isEmpty();
        List<AttackEffect> effects = new ArrayList<>();
        if (isAttack && falsifiableEffect) {
            effects.add(AttackEffect.DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN);
        }
        if (isAttack && commandTargetDropEffect) {
            effects.add(AttackEffect.COMMAND_TO_COMPROMISED_TARGET_IS_DROPPED);
        }
        if (isAttack && hasSelectedLink) {
            effects.add(AttackEffect.COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED);
        }
        return ModelSemanticsDto.builder()
                .attackPointUnit(AttackPointUnit.BEHAVIOR_CHANGING_DEVICE_INSTANCE_OR_AUTOMATION_LINK)
                .attackSelectionPolicy(switch (attackScenario.getMode()) {
                    case NONE -> AttackSelectionPolicy.NOT_MODELED;
                    case EXACT_POINTS -> AttackSelectionPolicy.EXACT_ATTACK_POINTS;
                    case ANY_UP_TO_BUDGET -> AttackSelectionPolicy.UP_TO_ATTACK_BUDGET_NONDETERMINISTIC;
                })
                .selectedAttackPoints(selectedAttackPoints(
                        attackScenario, deviceDisplayLabels, automationLinkDisplayLabels))
                .attackEffects(List.copyOf(effects))
                .modeledDeviceAttackPointCount(safeDeviceCount)
                .modeledFalsifiableReadingDeviceCount(safeFalsifiableReadingDeviceCount)
                .modeledAutomationLinkAttackPointCount(safeAutomationLinkCount)
                .modeledAttackPointCount(safeDeviceCount + safeAutomationLinkCount)
                .trustPropagationPolicy(
                        TrustPropagationPolicy.TARGET_UNTRUSTED_IF_ALL_TRIGGER_SOURCES_UNTRUSTED)
                .privacyPropagationPolicy(enablePrivacy
                        ? PrivacyPropagationPolicy.TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE
                        : PrivacyPropagationPolicy.NOT_MODELED)
                .labelPropagationScope(LabelPropagationScope.AUTOMATION_RULE_COMMANDS_ONLY)
                .environmentEvolutionEffects(List.of(
                        EnvironmentEvolutionEffect.DECLARED_NUMERIC_RATES_AND_DEVICE_EFFECTS_WITHIN_DOMAIN,
                        EnvironmentEvolutionEffect.DISCRETE_VALUES_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN))
                .localVariableFallbackPolicy(
                        LocalVariableFallbackPolicy.STUTTER_WHEN_NO_DECLARED_EVOLUTION)
                .build();
    }

    private static List<SelectedAttackPointDto> selectedAttackPoints(
            AttackScenarioDto attackScenario,
            Map<String, String> deviceDisplayLabels,
            Map<Long, String> automationLinkDisplayLabels) {
        if (attackScenario.getMode() != AttackScenarioDto.Mode.EXACT_POINTS
                || attackScenario.getPoints() == null) {
            return List.of();
        }
        Map<String, String> safeDeviceLabels = deviceDisplayLabels != null
                ? deviceDisplayLabels : Map.of();
        Map<Long, String> safeLinkLabels = automationLinkDisplayLabels != null
                ? automationLinkDisplayLabels : Map.of();
        List<SelectedAttackPointDto> result = new ArrayList<>();
        for (AttackPointDto point : attackScenario.getPoints()) {
            if (point == null) {
                continue;
            }
            result.add(SelectedAttackPointDto.builder()
                    .kind(point.getKind())
                    .deviceId(point.getDeviceId())
                    .ruleId(point.getRuleId())
                    .displayLabel(point.getKind() == AttackPointDto.Kind.DEVICE
                            ? safeDeviceLabels.get(point.getDeviceId())
                            : safeLinkLabels.get(point.getRuleId()))
                    .build());
        }
        return List.copyOf(result);
    }
}
