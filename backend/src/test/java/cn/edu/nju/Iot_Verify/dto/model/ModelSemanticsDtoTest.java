package cn.edu.nju.Iot_Verify.dto.model;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.AttackSurface;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ModelSemanticsDtoTest {

    @Test
    void attackRunDescribesUpperBoundSelectionAndDeclaredEffects() {
        ModelSemanticsDto semantics = ModelSemanticsDto.forRun(
                AttackScenarioDto.anyUpToBudget(1), true, 3, 4, 2);

        assertEquals(ModelSemanticsDto.AttackPointUnit.BEHAVIOR_CHANGING_DEVICE_INSTANCE_OR_AUTOMATION_LINK,
                semantics.getAttackPointUnit());
        assertEquals(ModelSemanticsDto.AttackSelectionPolicy.UP_TO_ATTACK_BUDGET_NONDETERMINISTIC,
                semantics.getAttackSelectionPolicy());
        assertTrue(semantics.getAttackEffects().contains(
                ModelSemanticsDto.AttackEffect.DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN));
        assertTrue(semantics.getAttackEffects().contains(
                ModelSemanticsDto.AttackEffect.COMMAND_TO_COMPROMISED_TARGET_IS_DROPPED));
        assertTrue(semantics.getAttackEffects().contains(
                ModelSemanticsDto.AttackEffect.COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED));
        assertEquals(
                ModelSemanticsDto.PrivacyPropagationPolicy
                        .TARGET_PRIVATE_IF_ANY_TRIGGER_OR_SELECTED_CONTENT_PRIVATE,
                semantics.getPrivacyPropagationPolicy());
        assertEquals(ModelSemanticsDto.LabelPropagationScope.AUTOMATION_RULE_COMMANDS_ONLY,
                semantics.getLabelPropagationScope());
        assertEquals(3, semantics.getModeledDeviceAttackPointCount());
        assertEquals(2, semantics.getModeledFalsifiableReadingDeviceCount());
        assertEquals(4, semantics.getModeledAutomationLinkAttackPointCount());
        assertEquals(7, semantics.getModeledAttackPointCount());
        assertEquals(List.of(
                        ModelSemanticsDto.EnvironmentEvolutionEffect
                                .DECLARED_NUMERIC_RATES_AND_DEVICE_EFFECTS_WITHIN_DOMAIN,
                        ModelSemanticsDto.EnvironmentEvolutionEffect
                                .DISCRETE_VALUES_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN),
                semantics.getEnvironmentEvolutionEffects());
        assertEquals(ModelSemanticsDto.LocalVariableFallbackPolicy
                        .STUTTER_WHEN_NO_DECLARED_EVOLUTION,
                semantics.getLocalVariableFallbackPolicy());
    }

    @Test
    void nonAttackRunDoesNotClaimAttackEffects() {
        ModelSemanticsDto semantics = ModelSemanticsDto.forRun(
                AttackScenarioDto.none(), false, 2, 1, 1);

        assertEquals(ModelSemanticsDto.AttackSelectionPolicy.NOT_MODELED,
                semantics.getAttackSelectionPolicy());
        assertTrue(semantics.getAttackEffects().isEmpty());
        assertEquals(ModelSemanticsDto.PrivacyPropagationPolicy.NOT_MODELED,
                semantics.getPrivacyPropagationPolicy());
        assertEquals(3, semantics.getModeledAttackPointCount());
    }

    @Test
    void attackRunDoesNotClaimReadingTamperingWhenSceneHasNoFalsifiableReading() {
        ModelSemanticsDto semantics = ModelSemanticsDto.forRun(
                AttackScenarioDto.anyUpToBudget(1), false, 1, 1, 0);

        assertEquals(List.of(
                ModelSemanticsDto.AttackEffect.COMMAND_TO_COMPROMISED_TARGET_IS_DROPPED,
                ModelSemanticsDto.AttackEffect.COMMAND_ON_COMPROMISED_AUTOMATION_LINK_IS_DROPPED),
                semantics.getAttackEffects());
    }

    @Test
    void attackRunDoesNotClaimCommandLossWhenSceneOnlyHasFalsifiableReading() {
        ModelSemanticsDto semantics = ModelSemanticsDto.forRun(
                AttackScenarioDto.anyUpToBudget(1), false, 1, 0, 1);

        assertEquals(List.of(
                ModelSemanticsDto.AttackEffect
                        .DECLARED_FALSIFIABLE_READING_NONDETERMINISTIC_WITHIN_DECLARED_DOMAIN),
                semantics.getAttackEffects());
    }

    @Test
    void exactRunCapturesDisplayLabelsWithoutChangingStablePointIdentity() {
        AttackScenarioDto scenario = AttackScenarioDto.exactPoints(List.of(
                AttackPointDto.device("sensor_1"),
                AttackPointDto.automationLink(7L)));
        AttackSurface surface = new AttackSurface(
                Set.of("sensor_1"), 1, Set.of("sensor_1"), Set.of(),
                Map.of("sensor_1", "Hall sensor"), Map.of(7L, "Turn on hall light"));

        ModelSemanticsDto semantics = ModelSemanticsDto.forRun(scenario, false, surface);

        assertEquals("sensor_1", semantics.getSelectedAttackPoints().get(0).getDeviceId());
        assertEquals(7L, semantics.getSelectedAttackPoints().get(1).getRuleId());
        assertEquals(List.of("Hall sensor", "Turn on hall light"),
                semantics.getSelectedAttackPoints().stream()
                        .map(SelectedAttackPointDto::getDisplayLabel).toList());
    }
}
