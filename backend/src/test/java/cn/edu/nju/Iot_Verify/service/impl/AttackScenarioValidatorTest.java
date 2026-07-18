package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.AttackSurface;
import cn.edu.nju.Iot_Verify.dto.model.AttackPointDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

class AttackScenarioValidatorTest {

    @Test
    void verificationCanonicalizesAndSortsExactPoints() {
        AttackScenarioDto scenario = AttackScenarioDto.exactPoints(List.of(
                AttackPointDto.automationLink(9L),
                AttackPointDto.device("light_1")));

        AttackScenarioDto canonical = AttackScenarioValidator.canonicalizeForVerification(scenario);

        assertEquals(AttackScenarioDto.Mode.EXACT_POINTS, canonical.getMode());
        assertEquals(List.of("AUTOMATION_LINK:9", "DEVICE:light_1"),
                canonical.getPoints().stream().map(AttackPointDto::identityKey).toList());
    }

    @Test
    void simulationRejectsExhaustiveBudgetSelection() {
        ValidationException error = assertThrows(ValidationException.class,
                () -> AttackScenarioValidator.canonicalizeForSimulation(
                        AttackScenarioDto.anyUpToBudget(2)));

        assertTrue(error.getMessage().contains("explicit attack points"));
    }

    @Test
    void exactPointsMustBelongToCurrentAttackSurfaceAndPersistedRules() {
        AttackSurface surface = new AttackSurface(
                Set.of("sensor_1", "light_1"), 1,
                Set.of("sensor_1"), Set.of("light_1"));
        RuleDto rule = RuleDto.builder().id(7L).build();

        AttackScenarioValidator.validateAgainstSurface(
                AttackScenarioDto.exactPoints(List.of(
                        AttackPointDto.device("light_1"),
                        AttackPointDto.automationLink(7L))),
                surface, List.of(rule));

        assertThrows(ValidationException.class, () -> AttackScenarioValidator.validateAgainstSurface(
                AttackScenarioDto.exactPoints(List.of(AttackPointDto.device("missing"))),
                surface, List.of(rule)));
        assertThrows(ValidationException.class, () -> AttackScenarioValidator.validateAgainstSurface(
                AttackScenarioDto.exactPoints(List.of(AttackPointDto.automationLink(8L))),
                surface, List.of(rule)));
        assertThrows(ValidationException.class, () -> AttackScenarioValidator.validateAgainstSurface(
                AttackScenarioDto.exactPoints(List.of(AttackPointDto.automationLink(7L))),
                surface, List.of(rule, RuleDto.builder().id(7L).build())));
    }

    @Test
    void exactDeviceIdsMustAlreadyUseNormalizedBoardIdentity() {
        ValidationException error = assertThrows(ValidationException.class,
                () -> AttackScenarioValidator.canonicalizeForVerification(
                        AttackScenarioDto.exactPoints(List.of(AttackPointDto.device("Living Room")))));

        assertTrue(error.getMessage().contains("normalized node id"));
    }
}
