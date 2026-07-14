package cn.edu.nju.Iot_Verify.dto.rule;

import jakarta.validation.ConstraintViolation;
import jakarta.validation.Validation;
import jakarta.validation.Validator;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class RuleDtoValidationTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();
    private final ObjectMapper objectMapper = new ObjectMapper();

    @Test
    void condition_relationWithoutValue_shouldReject() {
        RuleDto rule = validRuleWithCondition(RuleDto.Condition.builder()
                .deviceName("sensor")
                .attribute("temperature")
                .targetType("variable")
                .relation(">")
                .build());

        Set<ConstraintViolation<RuleDto>> violations = validator.validate(rule);

        assertTrue(hasViolationContaining(violations, "Value-based conditions require relation and value"));
    }

    @Test
    void condition_valueBasedWithoutRelation_shouldReject() {
        RuleDto rule = validRuleWithCondition(RuleDto.Condition.builder()
                .deviceName("sensor")
                .attribute("motion")
                .targetType("state")
                .build());

        Set<ConstraintViolation<RuleDto>> violations = validator.validate(rule);

        assertTrue(hasViolationContaining(violations, "Value-based conditions require relation and value"));
    }

    @Test
    void condition_apiWithoutRelationOrValue_shouldPass() {
        RuleDto rule = validRuleWithCondition(RuleDto.Condition.builder()
                .deviceName("sensor")
                .attribute("motionDetected")
                .targetType("api")
                .build());

        Set<ConstraintViolation<RuleDto>> violations = validator.validate(rule);

        assertFalse(hasViolationContaining(violations, "API signal conditions must not include relation or value"));
        assertFalse(hasViolationContaining(violations, "Value-based conditions require relation and value"));
    }

    @Test
    void condition_apiWithRelation_shouldReject() {
        RuleDto rule = validRuleWithCondition(RuleDto.Condition.builder()
                .deviceName("sensor")
                .attribute("motionDetected")
                .targetType("api")
                .relation("=")
                .value("TRUE")
                .build());

        Set<ConstraintViolation<RuleDto>> violations = validator.validate(rule);

        assertTrue(hasViolationContaining(violations, "API signal conditions must not include relation or value"));
    }

    @Test
    void condition_apiSerialization_shouldOmitNullRelationAndValue() throws Exception {
        RuleDto.Condition condition = RuleDto.Condition.builder()
                .deviceName("sensor")
                .attribute("motionDetected")
                .targetType("api")
                .build();

        String json = objectMapper.writeValueAsString(condition);

        assertFalse(json.contains("\"relation\""));
        assertFalse(json.contains("\"value\""));
    }

    @Test
    void ruleSerialization_shouldKeepOwnershipInternal() throws Exception {
        RuleDto rule = validRuleWithCondition(RuleDto.Condition.builder()
                .deviceName("sensor")
                .attribute("motionDetected")
                .targetType("api")
                .build());
        rule.setUserId(42L);

        String json = objectMapper.writeValueAsString(rule);

        assertFalse(json.contains("\"userId\""));
    }

    @Test
    void condition_relationAliasWithWhitespace_shouldPassBoundaryValidation() {
        RuleDto rule = validRuleWithCondition(RuleDto.Condition.builder()
                .deviceName("sensor")
                .attribute("temperature")
                .targetType("variable")
                .relation(" GTE ")
                .value("28")
                .build());

        Set<ConstraintViolation<RuleDto>> violations = validator.validate(rule);

        assertFalse(hasViolationContaining(violations, "Condition relation must be one of"));
        assertFalse(hasViolationContaining(violations, "Value-based conditions require relation and value"));
    }

    @Test
    void condition_nullElement_shouldReject() {
        RuleDto rule = RuleDto.builder()
                .conditions(Collections.singletonList(null))
                .command(RuleDto.Command.builder()
                        .deviceName("light")
                        .action("on")
                        .build())
                .build();

        Set<ConstraintViolation<RuleDto>> violations = validator.validate(rule);

        assertTrue(hasViolationContaining(violations, "Condition item cannot be null"));
    }

    @Test
    void command_contentSourceWithoutContent_shouldRejectInsteadOfBeingSilentlyIgnored() {
        RuleDto rule = validRuleWithCondition(RuleDto.Condition.builder()
                .deviceName("sensor")
                .attribute("motionDetected")
                .targetType("api")
                .build());
        rule.getCommand().setContentDevice("phone");

        Set<ConstraintViolation<RuleDto>> violations = validator.validate(rule);

        assertTrue(hasViolationContaining(violations,
                "contentDevice and content must be provided together"));
    }

    @Test
    void command_completeContentLabelFlow_shouldPassShapeValidation() {
        RuleDto rule = validRuleWithCondition(RuleDto.Condition.builder()
                .deviceName("sensor")
                .attribute("motionDetected")
                .targetType("api")
                .build());
        rule.getCommand().setContentDevice("phone");
        rule.getCommand().setContent("photo");

        Set<ConstraintViolation<RuleDto>> violations = validator.validate(rule);

        assertFalse(hasViolationContaining(violations,
                "contentDevice and content must be provided together"));
    }

    private RuleDto validRuleWithCondition(RuleDto.Condition condition) {
        return RuleDto.builder()
                .conditions(List.of(condition))
                .command(RuleDto.Command.builder()
                        .deviceName("light")
                        .action("on")
                        .build())
                .build();
    }

    private boolean hasViolationContaining(Set<? extends ConstraintViolation<?>> violations, String substring) {
        return violations.stream().anyMatch(v -> v.getMessage().contains(substring));
    }
}
