package cn.edu.nju.Iot_Verify.dto.model;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;
import java.util.ArrayList;

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
        int safeDeviceCount = Math.max(0, deviceCount);
        int safeAutomationLinkCount = Math.max(0, automationLinkCount);
        int safeFalsifiableReadingDeviceCount = Math.max(0,
                Math.min(falsifiableReadingDeviceCount, safeDeviceCount));
        List<AttackEffect> effects = new ArrayList<>();
        if (isAttack && safeFalsifiableReadingDeviceCount > 0) {
            effects.add(AttackEffect.DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN);
        }
        if (isAttack && safeAutomationLinkCount > 0) {
            effects.add(AttackEffect.COMMAND_TO_COMPROMISED_TARGET_IS_DROPPED);
            effects.add(AttackEffect.COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED);
        }
        return ModelSemanticsDto.builder()
                .attackPointUnit(AttackPointUnit.BEHAVIOR_CHANGING_DEVICE_INSTANCE_OR_AUTOMATION_LINK)
                .attackSelectionPolicy(isAttack
                        ? AttackSelectionPolicy.UP_TO_ATTACK_BUDGET_NONDETERMINISTIC
                        : AttackSelectionPolicy.NOT_MODELED)
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
}
