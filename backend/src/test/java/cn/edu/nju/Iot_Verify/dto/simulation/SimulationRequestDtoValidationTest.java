package cn.edu.nju.Iot_Verify.dto.simulation;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
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
    void playbackNodes_null_shouldReject() {
        SimulationRequestDto request = validRequest();
        request.setPlaybackNodes(null);

        Set<ConstraintViolation<SimulationRequestDto>> violations = validator.validate(request);

        assertTrue(hasFieldViolation(violations, "playbackNodes", "Playback nodes cannot be empty"));
    }

    @Test
    void playbackNodes_withNullElement_shouldReject() {
        SimulationRequestDto request = validRequest();
        request.setPlaybackNodes(Collections.singletonList(null));

        Set<ConstraintViolation<SimulationRequestDto>> violations = validator.validate(request);

        assertTrue(hasViolationContaining(violations, "Playback node item cannot be null"));
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
        request.setPlaybackNodes(List.of(validPlaybackNode()));
        request.setAttackScenario(AttackScenarioDto.none());
        return request;
    }

    private DeviceNodeDto validPlaybackNode() {
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("Lamp");
        node.setTemplateName("Switch");
        node.setLabel("Lamp");
        DeviceNodeDto.Position position = new DeviceNodeDto.Position();
        position.setX(10.0);
        position.setY(20.0);
        node.setPosition(position);
        node.setState("off");
        node.setWidth(160);
        node.setHeight(120);
        return node;
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

    private boolean hasFieldViolation(Set<? extends ConstraintViolation<?>> violations, String field, String message) {
        return violations.stream().anyMatch(v ->
                field.equals(v.getPropertyPath().toString()) && v.getMessage().contains(message));
    }
}
