package cn.edu.nju.Iot_Verify.component.aitool;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

class BoardSemanticValidatorTest {

    @Test
    void rejectsContradictoryStateAndModeConditions() {
        BoardSemanticValidator.BoardContext context = context();

        BoardSemanticValidator.GroupValidationIssue issue =
                BoardSemanticValidator.validateRuleConditionGroup(context, List.of(
                        ruleCondition("state", "state", "=", "heat;run"),
                        ruleCondition("mode", "MachineState", "=", "idle")
                ), null);

        assertEquals("CONTRADICTORY_CONDITION_GROUP", issue.reasonCode());
    }

    @Test
    void acceptsCompatiblePartialStateAndModeConditions() {
        BoardSemanticValidator.BoardContext context = context();

        BoardSemanticValidator.GroupValidationIssue issue =
                BoardSemanticValidator.validateRuleConditionGroup(context, List.of(
                        ruleCondition("state", "state", "=", "heat;_"),
                        ruleCondition("mode", "MachineState", "=", "run")
                ), null);

        assertNull(issue);
    }

    @Test
    void rejectsContradictoryNumericConditions() {
        BoardSemanticValidator.GroupValidationIssue issue =
                BoardSemanticValidator.validateSpecConditionGroup(context(), List.of(
                        specCondition("variable", "temperature", ">=", "10"),
                        specCondition("variable", "temperature", "<", "10")
                ), "if");

        assertEquals("CONTRADICTORY_CONDITION_GROUP", issue.reasonCode());
    }

    @Test
    void rejectsContradictoryFiniteDomainConditions() {
        BoardSemanticValidator.GroupValidationIssue issue =
                BoardSemanticValidator.validateSpecConditionGroup(context(), List.of(
                        specCondition("privacy", "MachineState", "=", "private"),
                        specCondition("privacy", "MachineState", "=", "public")
                ), "a");

        assertEquals("CONTRADICTORY_CONDITION_GROUP", issue.reasonCode());
    }

    @Test
    void rejectsCommandWhoseRequiredStartStateCannotMeetConditions() {
        RuleDto.Command command = RuleDto.Command.builder()
                .deviceName("device-1")
                .action("start")
                .build();

        BoardSemanticValidator.GroupValidationIssue issue =
                BoardSemanticValidator.validateRuleConditionGroup(context(), List.of(
                        ruleCondition("mode", "MachineState", "=", "run")
                ), command);

        assertEquals("COMMAND_PRESTATE_INCOMPATIBLE", issue.reasonCode());
    }

    @Test
    void wildcardCommandStartStateAcceptsAnySatisfiableTargetCondition() {
        BoardSemanticValidator.BoardContext context = context();
        context.templatesByName().get("heater").getManifest().getApis().get(0).setStartState("_");
        RuleDto.Command command = RuleDto.Command.builder()
                .deviceName("device-1")
                .action("start")
                .build();

        BoardSemanticValidator.GroupValidationIssue issue =
                BoardSemanticValidator.validateRuleConditionGroup(context, List.of(
                        ruleCondition("mode", "MachineState", "=", "run")
                ), command);

        assertNull(issue);
    }

    @Test
    void rejectsLegalStateThatIsUnreachableFromCurrentState() {
        BoardSemanticValidator.BoardContext context = context();
        context.nodesById().get("device-1").setState("eco;idle");

        BoardSemanticValidator.GroupValidationIssue issue =
                BoardSemanticValidator.validateSpecConditionGroup(context, List.of(
                        specCondition("state", "state", "=", "heat;run")
                ), "a");

        assertEquals("UNREACHABLE_CONDITION_GROUP", issue.reasonCode());
    }

    @Test
    void rejectsFixedVariableValueThatCannotChangeFromCurrentValue() {
        BoardSemanticValidator.BoardContext context = context();
        context.nodesById().get("device-1").setVariables(List.of(
                new VariableStateDto("temperature", "20", "trusted")));

        BoardSemanticValidator.GroupValidationIssue issue =
                BoardSemanticValidator.validateRuleConditionGroup(context, List.of(
                        ruleCondition("variable", "temperature", "=", "80")
                ), null);

        assertEquals("UNREACHABLE_CONDITION_GROUP", issue.reasonCode());
    }

    @Test
    void keepsOpenNumericDomainWhenNaturalChangeCanMoveTheValue() {
        BoardSemanticValidator.BoardContext context = context();
        context.nodesById().get("device-1").setVariables(List.of(
                new VariableStateDto("temperature", "20", "trusted")));
        context.templatesByName().get("heater").getManifest()
                .getInternalVariables().get(0).setNaturalChangeRate("[-1, 1]");

        BoardSemanticValidator.GroupValidationIssue issue =
                BoardSemanticValidator.validateRuleConditionGroup(context, List.of(
                        ruleCondition("variable", "temperature", "=", "80")
                ), null);

        assertNull(issue);
    }

    @Test
    void treatsZeroRateRangeAsFixed() {
        BoardSemanticValidator.BoardContext context = context();
        context.nodesById().get("device-1").setVariables(List.of(
                new VariableStateDto("temperature", "20", "trusted")));
        context.templatesByName().get("heater").getManifest()
                .getInternalVariables().get(0).setNaturalChangeRate("[0, 0]");

        BoardSemanticValidator.GroupValidationIssue issue =
                BoardSemanticValidator.validateRuleConditionGroup(context, List.of(
                        ruleCondition("variable", "temperature", "=", "80")
                ), null);

        assertEquals("UNREACHABLE_CONDITION_GROUP", issue.reasonCode());
    }

    @Test
    void rejectsCommandWhoseDeclaredStartStateIsUnreachable() {
        BoardSemanticValidator.BoardContext context = context();
        context.nodesById().get("device-1").setState("eco;idle");
        RuleDto.Command command = RuleDto.Command.builder()
                .deviceName("device-1")
                .action("start")
                .build();

        BoardSemanticValidator.GroupValidationIssue issue =
                BoardSemanticValidator.validateRuleConditionGroup(context, List.of(), command);

        assertEquals("COMMAND_PRESTATE_UNREACHABLE", issue.reasonCode());
    }

    private static BoardSemanticValidator.BoardContext context() {
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("device-1");
        node.setTemplateName("Heater");
        node.setLabel("Heater");

        DeviceTemplateDto.DeviceManifest manifest = DeviceTemplateDto.DeviceManifest.builder()
                .name("Heater")
                .modes(List.of("HeatMode", "MachineState"))
                .workingStates(List.of(
                        state("eco;idle"),
                        state("eco;run"),
                        state("heat;idle"),
                        state("heat;run")))
                .internalVariables(List.of(DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                        .name("temperature")
                        .isInside(true)
                        .falsifiableWhenCompromised(false)
                        .trust("trusted")
                        .privacy("public")
                        .lowerBound(0)
                        .upperBound(100)
                        .build()))
                .apis(List.of(DeviceTemplateDto.DeviceManifest.API.builder()
                        .name("start")
                        .signal(false)
                        .startState("heat;idle")
                        .endState("heat;run")
                        .build()))
                .build();
        DeviceTemplateDto template = new DeviceTemplateDto();
        template.setName("Heater");
        template.setManifest(manifest);
        return BoardSemanticValidator.recommendationContext(List.of(node), List.of(template), List.of());
    }

    private static DeviceTemplateDto.DeviceManifest.WorkingState state(String name) {
        return DeviceTemplateDto.DeviceManifest.WorkingState.builder()
                .name(name)
                .trust("trusted")
                .privacy("public")
                .dynamics(List.of())
                .build();
    }

    private static RuleDto.Condition ruleCondition(String targetType,
                                                   String attribute,
                                                   String relation,
                                                   String value) {
        return RuleDto.Condition.builder()
                .deviceName("device-1")
                .targetType(targetType)
                .attribute(attribute)
                .relation(relation)
                .value(value)
                .build();
    }

    private static SpecConditionDto specCondition(String targetType,
                                                  String key,
                                                  String relation,
                                                  String value) {
        SpecConditionDto condition = new SpecConditionDto();
        condition.setDeviceId("device-1");
        condition.setTargetType(targetType);
        condition.setKey(key);
        condition.setPropertyScope("privacy".equals(targetType) ? "state" : null);
        condition.setRelation(relation);
        condition.setValue(value);
        return condition;
    }
}
