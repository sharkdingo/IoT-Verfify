package cn.edu.nju.Iot_Verify.configure;

import jakarta.validation.ConstraintViolation;
import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class FuzzAdmissionConfigTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();

    @Test
    void defaultAllowsTwoActiveTasksPerUser() {
        FuzzAdmissionConfig config = new FuzzAdmissionConfig();

        assertEquals(2, config.getMaxActiveTasksPerUser());
        assertEquals(100, config.getMaxStoredTasksPerUser());
        assertTrue(validator.validate(config).isEmpty());
    }

    @Test
    void activeTaskLimitMustBePositive() {
        FuzzAdmissionConfig config = new FuzzAdmissionConfig();
        config.setMaxActiveTasksPerUser(0);

        Set<ConstraintViolation<FuzzAdmissionConfig>> violations = validator.validate(config);

        assertTrue(violations.stream().anyMatch(violation ->
                violation.getPropertyPath().toString().equals("maxActiveTasksPerUser")));
    }

    @Test
    void storedTaskLimitMustCoverTheActiveTaskLimit() {
        FuzzAdmissionConfig config = new FuzzAdmissionConfig();
        config.setMaxActiveTasksPerUser(3);
        config.setMaxStoredTasksPerUser(2);

        Set<ConstraintViolation<FuzzAdmissionConfig>> violations = validator.validate(config);

        assertTrue(violations.stream().anyMatch(violation ->
                violation.getMessage().contains("greater than or equal")));
    }
}
