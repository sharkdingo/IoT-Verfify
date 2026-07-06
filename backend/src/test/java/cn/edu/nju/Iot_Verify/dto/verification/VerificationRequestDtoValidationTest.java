package cn.edu.nju.Iot_Verify.dto.verification;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import jakarta.validation.ConstraintViolation;
import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class VerificationRequestDtoValidationTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();

    @Test
    void specs_null_shouldReject() {
        VerificationRequestDto request = validRequest();
        request.setSpecs(null);

        Set<ConstraintViolation<VerificationRequestDto>> violations = validator.validate(request);

        assertTrue(hasFieldViolation(violations, "specs", "Specs list cannot be empty"));
    }

    @Test
    void specs_empty_shouldReject() {
        VerificationRequestDto request = validRequest();
        request.setSpecs(List.of());

        Set<ConstraintViolation<VerificationRequestDto>> violations = validator.validate(request);

        assertTrue(hasFieldViolation(violations, "specs", "Specs list cannot be empty"));
    }

    @Test
    void devices_withNullElement_shouldReject() {
        VerificationRequestDto request = validRequest();
        request.setDevices(Collections.singletonList(null));

        Set<ConstraintViolation<VerificationRequestDto>> violations = validator.validate(request);

        assertTrue(hasViolationContaining(violations, "Device item cannot be null"));
    }

    @Test
    void specs_withNullElement_shouldReject() {
        VerificationRequestDto request = validRequest();
        request.setSpecs(Collections.singletonList(null));

        Set<ConstraintViolation<VerificationRequestDto>> violations = validator.validate(request);

        assertTrue(hasViolationContaining(violations, "Specification item cannot be null"));
    }

    @Test
    void rules_withNullElement_shouldReject() {
        VerificationRequestDto request = validRequest();
        request.setRules(Collections.singletonList(null));

        Set<ConstraintViolation<VerificationRequestDto>> violations = validator.validate(request);

        assertTrue(hasViolationContaining(violations, "Rule item cannot be null"));
    }

    @Test
    void specs_withOneSpec_shouldPassListConstraint() {
        VerificationRequestDto request = validRequest();

        Set<ConstraintViolation<VerificationRequestDto>> violations = validator.validate(request);

        assertFalse(hasFieldViolation(violations, "specs", "Specs list cannot be empty"));
    }

    private VerificationRequestDto validRequest() {
        VerificationRequestDto request = new VerificationRequestDto();
        request.setDevices(List.of(validDevice()));
        request.setSpecs(List.of(validSpec()));
        return request;
    }

    private DeviceVerificationDto validDevice() {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("Lamp");
        device.setTemplateName("Switch");
        device.setState("off");
        return device;
    }

    private SpecificationDto validSpec() {
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_1");
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        return spec;
    }

    private boolean hasFieldViolation(Set<? extends ConstraintViolation<?>> violations, String field, String message) {
        return violations.stream().anyMatch(v ->
                field.equals(v.getPropertyPath().toString()) && v.getMessage().contains(message));
    }

    private boolean hasViolationContaining(Set<? extends ConstraintViolation<?>> violations, String message) {
        return violations.stream().anyMatch(v -> v.getMessage().contains(message));
    }
}
