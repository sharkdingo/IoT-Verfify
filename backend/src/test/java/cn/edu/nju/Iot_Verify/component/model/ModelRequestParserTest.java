package cn.edu.nju.Iot_Verify.component.model;

import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import jakarta.validation.Validation;
import jakarta.validation.ConstraintViolationException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;
import static org.junit.jupiter.api.Assertions.assertThrows;

class ModelRequestParserTest {

    private final ObjectMapper objectMapper = new ObjectMapper();
    private ModelRequestParser parser;

    @BeforeEach
    void setUp() {
        parser = new ModelRequestParser(
                objectMapper,
                Validation.buildDefaultValidatorFactory().getValidator());
    }

    @Test
    void verificationRejectsMisspelledAttackFlagInsteadOfSilentlyDisablingAttackModeling() throws Exception {
        JsonNode body = objectMapper.readTree("""
                {
                  "attackEnabled": true
                }
                """);

        BadRequestException exception = assertThrows(
                BadRequestException.class, () -> parser.parseVerification(body));

        assertThat(exception.getMessage())
                .contains("attackEnabled")
                .contains("ignoring it could change what the model checks");
    }

    @Test
    void verificationRejectsUnknownNestedRuntimeFieldWithExactPath() throws Exception {
        // Devices are no longer client input, so the nested-path guarantee is pinned on the one
        // nested structure a run request still owns: its attack selection.
        JsonNode body = objectMapper.readTree("""
                {
                  "attackScenario": {"mode": "EXACT_POINTS", "points": [{"kind": "DEVICE", "devceId": "x"}]}
                }
                """);

        BadRequestException exception = assertThrows(
                BadRequestException.class, () -> parser.parseVerification(body));

        assertThat(exception.getMessage())
                .contains("devceId")
                .contains("attackScenario.points[0].devceId");
    }

    @Test
    void simulationRejectsMisspelledPrivacyFlagInsteadOfSilentlyDisablingPropagation() throws Exception {
        JsonNode body = objectMapper.readTree("""
                {
                  "privacyEnabled": true
                }
                """);

        BadRequestException exception = assertThrows(
                BadRequestException.class, () -> parser.parseSimulation(body));

        assertThat(exception.getMessage()).contains("privacyEnabled");
    }

    @Test
    void beanValidationStillRunsAfterStrictParsing() throws Exception {
        JsonNode body = objectMapper.readTree("""
                {
                  "steps": 10
                }
                """);

        ConstraintViolationException exception = assertThrows(
                ConstraintViolationException.class, () -> parser.parseSimulation(body));

        // attackScenario is the required run parameter; the scene is not validated here because the
        // server supplies it from the board.
        assertThat(exception.getConstraintViolations())
                .anySatisfy(violation -> assertThat(violation.getPropertyPath().toString())
                        .isEqualTo("attackScenario"));
    }
}
