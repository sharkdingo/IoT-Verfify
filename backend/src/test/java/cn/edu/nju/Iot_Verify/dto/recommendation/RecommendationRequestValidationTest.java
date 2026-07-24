package cn.edu.nju.Iot_Verify.dto.recommendation;

import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class RecommendationRequestValidationTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();

    @Test
    void scenarioRequirement_acceptsDetailedPromptUpToDocumentedLimit() {
        ScenarioRecommendationRequestDto request = validScenarioRequest();
        request.setUserRequirement("x".repeat(RecommendationLimits.MAX_USER_REQUIREMENT_LENGTH));

        assertTrue(validator.validate(request).isEmpty());

        request.setUserRequirement("x".repeat(RecommendationLimits.MAX_USER_REQUIREMENT_LENGTH + 1));
        assertFalse(validator.validate(request).isEmpty());
    }

    @Test
    void scenarioRequest_requiresExplicitMinimumAndMaximumTargets() {
        ScenarioRecommendationRequestDto request = new ScenarioRecommendationRequestDto();

        assertFalse(validator.validate(request).isEmpty());
    }

    @Test
    void scenarioRequest_rejectsMinimumAboveMaximum() {
        ScenarioRecommendationRequestDto request = validScenarioRequest();
        request.setMinDevices(4);
        request.setMaxDevices(3);

        assertFalse(validator.validate(request).isEmpty());
    }

    @Test
    void deviceRequirement_usesSameRecommendationLimit() {
        DeviceRecommendationRequestDto request = new DeviceRecommendationRequestDto();
        request.setUserRequirement("x".repeat(RecommendationLimits.MAX_USER_REQUIREMENT_LENGTH));

        assertTrue(validator.validate(request).isEmpty());

        request.setUserRequirement("x".repeat(RecommendationLimits.MAX_USER_REQUIREMENT_LENGTH + 1));
        assertFalse(validator.validate(request).isEmpty());
    }

    @Test
    void standaloneRequestId_usesTheSharedInteractiveRequestContract() {
        StandaloneRecommendationRequestDto request = new StandaloneRecommendationRequestDto();
        request.setRequestId("request.v1:part");

        assertTrue(validator.validate(request).isEmpty());

        request.setRequestId("request/v1");
        assertFalse(validator.validate(request).isEmpty());
    }

    private ScenarioRecommendationRequestDto validScenarioRequest() {
        ScenarioRecommendationRequestDto request = new ScenarioRecommendationRequestDto();
        request.setMinDevices(1);
        request.setMinRules(1);
        request.setMinSpecs(1);
        request.setMaxDevices(6);
        request.setMaxRules(5);
        request.setMaxSpecs(5);
        return request;
    }
}
