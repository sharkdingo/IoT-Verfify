package cn.edu.nju.Iot_Verify.dto.board;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.exc.InvalidNullException;
import jakarta.validation.ConstraintViolation;
import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.assertThrows;

class EnvironmentVariableUpdateRequestDtoValidationTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();
    private final ObjectMapper objectMapper = new ObjectMapper();

    @Test
    void acceptsCompleteExpectedValueAndAnOmittedDesiredValue() {
        EnvironmentVariableUpdateRequestDto request = new EnvironmentVariableUpdateRequestDto(
                "temperature",
                new EnvironmentVariableUpdateRequestDto.ExpectedValue(
                        "27", "trusted", "public"),
                new EnvironmentVariableUpdateRequestDto.DesiredPatch(
                        null, "untrusted", null));

        assertTrue(validator.validate(request).isEmpty());
    }

    @Test
    void requiresCompleteExpectedLabelsAndAtLeastOneDesiredField() {
        EnvironmentVariableUpdateRequestDto request = new EnvironmentVariableUpdateRequestDto(
                "temperature",
                new EnvironmentVariableUpdateRequestDto.ExpectedValue(" ", null, " "),
                new EnvironmentVariableUpdateRequestDto.DesiredPatch(null, null, null));

        Set<ConstraintViolation<EnvironmentVariableUpdateRequestDto>> violations =
                validator.validate(request);

        assertTrue(violations.stream().anyMatch(v -> v.getPropertyPath().toString()
                .equals("expected.value")));
        assertTrue(violations.stream().anyMatch(v -> v.getPropertyPath().toString()
                .equals("expected.trust")));
        assertTrue(violations.stream().anyMatch(v -> v.getPropertyPath().toString()
                .equals("expected.privacy")));
        assertTrue(violations.stream().anyMatch(v -> v.getPropertyPath().toString()
                .equals("desired.fieldProvided")));
    }

    @Test
    void rejectsAnOmittedOrNullExpectedValue() throws Exception {
        EnvironmentVariableUpdateRequestDto omitted = objectMapper.readValue(
                "{\"name\":\"signal\",\"expected\":{\"trust\":\"untrusted\",\"privacy\":\"public\"},"
                        + "\"desired\":{\"trust\":\"trusted\"}}",
                EnvironmentVariableUpdateRequestDto.class);
        EnvironmentVariableUpdateRequestDto explicitNull = objectMapper.readValue(
                "{\"name\":\"signal\",\"expected\":{\"value\":null,\"trust\":\"untrusted\",\"privacy\":\"public\"},"
                        + "\"desired\":{\"trust\":\"trusted\"}}",
                EnvironmentVariableUpdateRequestDto.class);

        assertTrue(validator.validate(omitted).stream().anyMatch(violation ->
                violation.getPropertyPath().toString().equals("expected.value")));
        assertTrue(validator.validate(explicitNull).stream().anyMatch(violation ->
                violation.getPropertyPath().toString().equals("expected.value")));
    }

    @Test
    void allowsAnOmittedDesiredValueToPreserveTheCurrentValue() throws Exception {
        String json = "{\"name\":\"signal\","
                + "\"expected\":{\"value\":\"old\",\"trust\":\"untrusted\",\"privacy\":\"public\"},"
                + "\"desired\":{\"trust\":\"trusted\"}}";

        EnvironmentVariableUpdateRequestDto request = objectMapper.readValue(
                json, EnvironmentVariableUpdateRequestDto.class);

        assertNull(request.getDesired().getValue());
        assertTrue(validator.validate(request).isEmpty());
    }

    @Test
    void rejectsExplicitNullDesiredValue() {
        String json = "{\"name\":\"signal\","
                + "\"expected\":{\"value\":\"old\",\"trust\":\"untrusted\",\"privacy\":\"public\"},"
                + "\"desired\":{\"value\":null}}";

        assertThrows(InvalidNullException.class, () -> objectMapper.readValue(
                json, EnvironmentVariableUpdateRequestDto.class));
    }

    @Test
    void rejectsExplicitNullDesiredSecurityLabels() {
        String json = "{\"name\":\"signal\","
                + "\"expected\":{\"value\":\"old\",\"trust\":\"untrusted\",\"privacy\":\"public\"},"
                + "\"desired\":{\"trust\":null}}";

        assertThrows(InvalidNullException.class, () -> objectMapper.readValue(
                json, EnvironmentVariableUpdateRequestDto.class));
    }
}
