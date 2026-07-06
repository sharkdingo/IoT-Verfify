package cn.edu.nju.Iot_Verify.dto.spec;

import jakarta.validation.ConstraintViolation;
import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class SpecificationDtoValidationTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();

    @Test
    void deviceRef_withoutIdOrLabel_shouldReject() {
        SpecificationDto spec = validSpec();
        spec.setDevices(List.of(new SpecificationDto.DeviceRefDto(null, null, List.of())));

        Set<ConstraintViolation<SpecificationDto>> violations = validator.validate(spec);

        assertTrue(hasViolationContaining(violations, "Specification device must include deviceId or deviceLabel"));
    }

    @Test
    void deviceRef_withLabel_shouldPassReferenceCheck() {
        SpecificationDto spec = validSpec();
        spec.setDevices(List.of(new SpecificationDto.DeviceRefDto(null, "Kitchen Light", List.of())));

        Set<ConstraintViolation<SpecificationDto>> violations = validator.validate(spec);

        assertFalse(hasViolationContaining(violations, "Specification device must include deviceId or deviceLabel"));
    }

    @Test
    void condition_withUnsupportedSide_shouldReject() {
        SpecificationDto spec = validSpec();
        spec.setAConditions(List.of(validCondition("before")));

        Set<ConstraintViolation<SpecificationDto>> violations = validator.validate(spec);

        assertTrue(hasViolationContaining(violations, "Side must be one of: a, if, then"));
    }

    @Test
    void condition_nullElement_shouldReject() {
        SpecificationDto spec = validSpec();
        spec.setAConditions(Collections.singletonList(null));

        Set<ConstraintViolation<SpecificationDto>> violations = validator.validate(spec);

        assertTrue(hasViolationContaining(violations, "A-condition item cannot be null"));
    }

    @Test
    void deviceRef_nullElement_shouldReject() {
        SpecificationDto spec = validSpec();
        spec.setDevices(Collections.singletonList(null));

        Set<ConstraintViolation<SpecificationDto>> violations = validator.validate(spec);

        assertTrue(hasViolationContaining(violations, "Specification device item cannot be null"));
    }

    @Test
    void selectedApis_nullElement_shouldReject() {
        SpecificationDto spec = validSpec();
        spec.setDevices(List.of(new SpecificationDto.DeviceRefDto("light", null, Collections.singletonList(null))));

        Set<ConstraintViolation<SpecificationDto>> violations = validator.validate(spec);

        assertTrue(hasViolationContaining(violations, "Selected API name cannot be null"));
    }

    @Test
    void condition_sideMustMatchContainingCollection() {
        SpecificationDto spec = validSpec();
        spec.setIfConditions(List.of(validCondition("then")));

        Set<ConstraintViolation<SpecificationDto>> violations = validator.validate(spec);

        assertTrue(hasViolationContaining(violations, "Specification condition side must match its containing collection"));
    }

    @Test
    void condition_sideMayBeOmittedBecauseCollectionIsAuthoritative() {
        SpecificationDto spec = validSpec();
        spec.setThenConditions(List.of(validCondition(null)));

        Set<ConstraintViolation<SpecificationDto>> violations = validator.validate(spec);

        assertFalse(hasViolationContaining(violations, "Side must be one of: a, if, then"));
        assertFalse(hasViolationContaining(violations, "Specification condition side must match its containing collection"));
    }

    private SpecificationDto validSpec() {
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_1");
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        return spec;
    }

    private SpecConditionDto validCondition(String side) {
        SpecConditionDto condition = new SpecConditionDto();
        condition.setId("cond_1");
        condition.setSide(side);
        condition.setDeviceId("light");
        condition.setTargetType("state");
        condition.setKey("state");
        condition.setRelation("=");
        condition.setValue("on");
        return condition;
    }

    private boolean hasViolationContaining(Set<? extends ConstraintViolation<?>> violations, String substring) {
        return violations.stream().anyMatch(v -> v.getMessage().contains(substring));
    }
}
