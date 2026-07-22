package cn.edu.nju.Iot_Verify.configure;

import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ChatExecutionConfigTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();

    @Test
    void defaults_shouldReserveOneCompleteWorstCaseTurn() {
        assertTrue(validator.validate(new ChatExecutionConfig()).isEmpty());
    }

    @Test
    void messageLimitBelowWorstCaseReserve_shouldFailValidation() {
        ChatExecutionConfig config = new ChatExecutionConfig();
        config.setMaxMessagesPerSession(1_000);

        assertFalse(validator.validate(config).isEmpty());
    }
}
