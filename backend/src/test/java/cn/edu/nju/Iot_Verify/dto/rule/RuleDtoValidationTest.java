package cn.edu.nju.Iot_Verify.dto.rule;

import jakarta.validation.ConstraintViolation;
import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class RuleDtoValidationTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();

    @Test
    void condition_relationWithoutValue_shouldReject() {
        RuleDto rule = validRuleWithCondition(RuleDto.Condition.builder()
                .deviceName("sensor")
                .attribute("temperature")
                .relation(">")
                .build());

        Set<ConstraintViolation<RuleDto>> violations = validator.validate(rule);

        assertTrue(hasViolationContaining(violations, "Condition value is required when relation is provided"));
    }

    @Test
    void condition_withoutRelationMayOmitValue() {
        RuleDto rule = validRuleWithCondition(RuleDto.Condition.builder()
                .deviceName("sensor")
                .attribute("motion")
                .build());

        Set<ConstraintViolation<RuleDto>> violations = validator.validate(rule);

        assertFalse(hasViolationContaining(violations, "Condition value is required when relation is provided"));
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
