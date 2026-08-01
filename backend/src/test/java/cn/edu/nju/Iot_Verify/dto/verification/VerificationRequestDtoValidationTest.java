package cn.edu.nju.Iot_Verify.dto.verification;

import cn.edu.nju.Iot_Verify.component.model.ModelRequestParser;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationRequestDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import com.fasterxml.jackson.databind.ObjectMapper;
import jakarta.validation.ConstraintViolationException;
import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run request carries run <em>parameters</em>; the scene comes from the caller's persisted board.
 *
 * <p>This boundary closed an authority inversion. While devices/rules/specs/environment were request
 * fields, an account whose board held no devices could post a fabricated two-device scene and have
 * the resulting VIOLATED verdict persisted into its own run history, where the UI presents a run as
 * "this saved scene was checked". These tests pin that the boundary now <em>refuses</em> any attempt
 * to describe the scene, instead of validating the shape of a scene it should never have accepted.
 */
class VerificationRequestDtoValidationTest {

    private static final ObjectMapper JSON = new ObjectMapper();

    private final ModelRequestParser parser = newParser();

    private static ModelRequestParser newParser() {
        Validator validator = Validation.buildDefaultValidatorFactory().getValidator();
        return new ModelRequestParser(new ObjectMapper().findAndRegisterModules(), validator);
    }

    private BadRequestException rejected(String json, boolean verification) {
        return assertThrows(BadRequestException.class, () -> {
            if (verification) {
                parser.parseVerification(JSON.readTree(json));
            } else {
                parser.parseSimulation(JSON.readTree(json));
            }
        });
    }

    @Test
    void aClientSuppliedSceneIsRefusedRatherThanVerified() {
        for (String sceneField : new String[]{"devices", "rules", "specs", "environmentVariables",
                "playbackNodes"}) {
            BadRequestException rejection = rejected(
                    "{\"attackScenario\":{\"mode\":\"NONE\",\"points\":[]},"
                            + "\"enablePrivacy\":false,\"" + sceneField + "\":[]}", true);
            assertTrue(rejection.getMessage().contains(sceneField),
                    () -> "supplying '" + sceneField + "' must be refused, got: "
                            + rejection.getMessage());
        }
    }

    @Test
    void aSimulationRequestRefusesTheSameSceneFields() {
        for (String sceneField : new String[]{"devices", "rules", "environmentVariables",
                "playbackNodes"}) {
            BadRequestException rejection = rejected(
                    "{\"steps\":5,\"attackScenario\":{\"mode\":\"NONE\",\"points\":[]},"
                            + "\"enablePrivacy\":false,\"" + sceneField + "\":[]}", false);
            assertTrue(rejection.getMessage().contains(sceneField),
                    () -> "supplying '" + sceneField + "' must be refused, got: "
                            + rejection.getMessage());
        }
    }

    @Test
    void runParametersAloneAreAccepted() {
        VerificationRequestDto verification = assertDoesNotThrow(() ->
                parser.parseVerification(JSON.readTree(
                        "{\"attackScenario\":{\"mode\":\"NONE\",\"points\":[]},\"enablePrivacy\":true}")));
        assertNotNull(verification.getAttackScenario());
        assertTrue(verification.isEnablePrivacy());
        // Nothing here describes the scene; the service fills it in from the board read.
        assertNull(verification.getDevices());
        assertNull(verification.getSpecs());
        assertNull(verification.getPlaybackNodes());

        SimulationRequestDto simulation = assertDoesNotThrow(() ->
                parser.parseSimulation(JSON.readTree(
                        "{\"steps\":7,\"attackScenario\":{\"mode\":\"NONE\",\"points\":[]}}")));
        assertEquals(7, simulation.getSteps());
        assertNull(simulation.getDevices());
        assertNull(simulation.getPlaybackNodes());
    }

    @Test
    void runParametersAreStillValidated() {
        // Bean violations stay ConstraintViolationException so the REST layer keeps mapping DTO shape
        // problems to 400, separately from the services' 422 model-semantic errors.
        ConstraintViolationException missingScenario = assertThrows(ConstraintViolationException.class,
                () -> parser.parseVerification(JSON.readTree("{\"enablePrivacy\":false}")));
        assertTrue(missingScenario.getMessage().toLowerCase().contains("attack"),
                () -> "attackScenario is still required: " + missingScenario.getMessage());

        ConstraintViolationException badSteps = assertThrows(ConstraintViolationException.class,
                () -> parser.parseSimulation(JSON.readTree(
                        "{\"steps\":0,\"attackScenario\":{\"mode\":\"NONE\",\"points\":[]}}")));
        assertNotNull(badSteps.getConstraintViolations());
        assertTrue(badSteps.getConstraintViolations().stream()
                        .anyMatch(violation -> violation.getPropertyPath().toString().contains("steps")),
                () -> "steps bounds still apply: " + badSteps.getMessage());
    }
}
