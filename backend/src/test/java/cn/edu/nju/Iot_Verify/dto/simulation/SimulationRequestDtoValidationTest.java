package cn.edu.nju.Iot_Verify.dto.simulation;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import jakarta.validation.ConstraintViolation;
import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import java.util.Collections;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertTrue;

class SimulationRequestDtoValidationTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();

    @Test
    void devices_withNullElement_shouldReject() {
        SimulationRequestDto request = validRequest();
        request.setDevices(Collections.singletonList(null));

        Set<ConstraintViolation<SimulationRequestDto>> violations = validator.validate(request);

        assertTrue(hasViolationContaining(violations, "Device item cannot be null"));
    }

    @Test
    void rules_withNullElement_shouldReject() {
        SimulationRequestDto request = validRequest();
        request.setRules(Collections.singletonList(null));

        Set<ConstraintViolation<SimulationRequestDto>> violations = validator.validate(request);

        assertTrue(hasViolationContaining(violations, "Rule item cannot be null"));
    }

    private SimulationRequestDto validRequest() {
        SimulationRequestDto request = new SimulationRequestDto();
        request.setDevices(List.of(validDevice()));
        return request;
    }

    private DeviceVerificationDto validDevice() {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("Lamp");
        device.setTemplateName("Switch");
        return device;
    }

    private boolean hasViolationContaining(Set<? extends ConstraintViolation<?>> violations, String message) {
        return violations.stream().anyMatch(v -> v.getMessage().contains(message));
    }
}
