package cn.edu.nju.Iot_Verify.dto.auth;

import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class RegisterRequestDtoValidationTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();

    @Test
    void usernameLength_shouldBeCheckedAfterNormalization() {
        RegisterRequestDto request = validRequest("  " + "a".repeat(20) + "  ");

        assertTrue(validator.validate(request).isEmpty());
    }

    @Test
    void username_shouldRejectShortNormalizedAndControlCharacterValues() {
        assertFalse(validator.validate(validRequest("  ab  ")).isEmpty());
        assertFalse(validator.validate(validRequest("Ali\nce")).isEmpty());
        assertFalse(validator.validate(validRequest("Ali\u200bce")).isEmpty());
        assertTrue(validator.validate(validRequest("\ud83d\udca1\ud83c\udfe0\ud83d\udd12")).isEmpty());
    }

    private RegisterRequestDto validRequest(String username) {
        RegisterRequestDto request = new RegisterRequestDto();
        request.setPhone("13800138000");
        request.setUsername(username);
        request.setPassword("password123");
        return request;
    }
}
