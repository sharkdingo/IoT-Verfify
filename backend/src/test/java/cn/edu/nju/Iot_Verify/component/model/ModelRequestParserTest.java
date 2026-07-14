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
                  "devices": [{"varName": "sensor_1", "templateName": "Sensor"}],
                  "specs": [{
                    "id": "spec-1",
                    "templateId": "3",
                    "templateLabel": "Never",
                    "aConditions": [],
                    "ifConditions": [],
                    "thenConditions": [],
                    "devices": []
                  }],
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
        JsonNode body = objectMapper.readTree("""
                {
                  "devices": [{
                    "varName": "sensor_1",
                    "templateName": "Sensor",
                    "currentStateTrsut": "untrusted"
                  }],
                  "specs": [{
                    "id": "spec-1",
                    "templateId": "3",
                    "templateLabel": "Never",
                    "aConditions": [],
                    "ifConditions": [],
                    "thenConditions": [],
                    "devices": []
                  }]
                }
                """);

        BadRequestException exception = assertThrows(
                BadRequestException.class, () -> parser.parseVerification(body));

        assertThat(exception.getMessage())
                .contains("currentStateTrsut")
                .contains("devices[0].currentStateTrsut");
    }

    @Test
    void simulationRejectsMisspelledPrivacyFlagInsteadOfSilentlyDisablingPropagation() throws Exception {
        JsonNode body = objectMapper.readTree("""
                {
                  "devices": [{"varName": "sensor_1", "templateName": "Sensor"}],
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
                  "devices": [],
                  "steps": 10
                }
                """);

        ConstraintViolationException exception = assertThrows(
                ConstraintViolationException.class, () -> parser.parseSimulation(body));

        assertThat(exception.getConstraintViolations())
                .anySatisfy(violation -> assertThat(violation.getPropertyPath().toString())
                        .isEqualTo("devices"));
    }
}
