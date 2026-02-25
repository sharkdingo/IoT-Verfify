package cn.edu.nju.Iot_Verify.configure;

import jakarta.validation.ConstraintViolation;
import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertTrue;

class ThreadPoolConfigValidationTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();

    @Test
    void defaultConfig_shouldBeValid() {
        ThreadPoolConfig config = new ThreadPoolConfig();

        Set<ConstraintViolation<ThreadPoolConfig>> violations = validator.validate(config);

        assertTrue(violations.isEmpty());
    }

    @Test
    void poolWithCoreLargerThanMax_shouldBeInvalid() {
        ThreadPoolConfig config = new ThreadPoolConfig();
        config.getSyncSimulation().setCorePoolSize(8);
        config.getSyncSimulation().setMaxPoolSize(4);

        Set<ConstraintViolation<ThreadPoolConfig>> violations = validator.validate(config);

        assertTrue(violations.stream()
                .anyMatch(v -> v.getMessage().contains("less than or equal")));
    }

    @Test
    void poolWithNegativeQueue_shouldBeInvalid() {
        ThreadPoolConfig config = new ThreadPoolConfig();
        config.getChat().setQueueCapacity(-1);

        Set<ConstraintViolation<ThreadPoolConfig>> violations = validator.validate(config);

        assertTrue(violations.stream()
                .anyMatch(v -> v.getPropertyPath().toString().contains("queueCapacity")));
    }
}
