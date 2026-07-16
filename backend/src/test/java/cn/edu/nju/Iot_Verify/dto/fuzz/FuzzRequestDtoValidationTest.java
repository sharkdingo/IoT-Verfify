package cn.edu.nju.Iot_Verify.dto.fuzz;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import jakarta.validation.ConstraintViolation;
import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class FuzzRequestDtoValidationTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();
    private final ObjectMapper objectMapper = new ObjectMapper();

    @Test
    void defaultsAreWithinTheBoundedWorkload() {
        FuzzRequestDto request = new FuzzRequestDto();

        assertTrue(validator.validate(request).isEmpty());
        assertEquals(FuzzExplorationMode.BOARD_SNAPSHOT, request.getExplorationMode());
    }

    @Test
    void jsonContractDefaultsMissingModeAndAcceptsExplicitPaperCompatibleMode() throws Exception {
        FuzzRequestDto defaultRequest = objectMapper.readValue("{}", FuzzRequestDto.class);
        FuzzRequestDto paperRequest = objectMapper.readValue(
                "{\"explorationMode\":\"PAPER_COMPATIBLE\","
                        + "\"paperDomainFingerprint\":\"" + "a".repeat(64) + "\"}",
                FuzzRequestDto.class);

        assertEquals(FuzzExplorationMode.BOARD_SNAPSHOT, defaultRequest.getExplorationMode());
        assertEquals(FuzzExplorationMode.PAPER_COMPATIBLE, paperRequest.getExplorationMode());
        assertTrue(validator.validate(defaultRequest).isEmpty());
        assertTrue(validator.validate(paperRequest).isEmpty());
    }

    @Test
    void paperDomainPreviewDefaultsMissingPathLengthButRejectsExplicitNull() throws Exception {
        FuzzPaperDomainPreviewRequestDto defaultRequest = objectMapper.readValue(
                "{}", FuzzPaperDomainPreviewRequestDto.class);
        FuzzPaperDomainPreviewRequestDto explicitNull = objectMapper.readValue(
                "{\"pathLength\":null}", FuzzPaperDomainPreviewRequestDto.class);

        assertEquals(20, defaultRequest.getPathLength());
        assertTrue(validator.validate(defaultRequest).isEmpty());
        assertTrue(validator.validate(explicitNull).stream()
                .anyMatch(violation -> violation.getPropertyPath().toString().equals("pathLength")));
    }

    @Test
    void validatesPaperDomainFingerprintShapeWhenProvided() {
        FuzzRequestDto malformed = new FuzzRequestDto();
        malformed.setExplorationMode(FuzzExplorationMode.PAPER_COMPATIBLE);
        malformed.setPaperDomainFingerprint("ABC");
        FuzzRequestDto valid = new FuzzRequestDto();
        valid.setExplorationMode(FuzzExplorationMode.PAPER_COMPATIBLE);
        valid.setPaperDomainFingerprint("b".repeat(64));

        assertTrue(hasProperty(validator.validate(malformed), "paperDomainFingerprint"));
        assertFalse(hasProperty(validator.validate(valid), "paperDomainFingerprint"));
    }

    @Test
    void responseDtosSerializeExplorationModeByItsStableEnumName() throws Exception {
        List<Object> responses = List.of(
                FuzzTaskDto.builder().explorationMode(FuzzExplorationMode.PAPER_COMPATIBLE).build(),
                FuzzTaskSummaryDto.builder().explorationMode(FuzzExplorationMode.PAPER_COMPATIBLE).build(),
                FuzzRunDto.builder().explorationMode(FuzzExplorationMode.PAPER_COMPATIBLE).build(),
                FuzzRunSummaryDto.builder().explorationMode(FuzzExplorationMode.PAPER_COMPATIBLE).build());

        for (Object response : responses) {
            JsonNode json = objectMapper.readTree(objectMapper.writeValueAsString(response));
            assertEquals("PAPER_COMPATIBLE", json.path("explorationMode").asText());
        }
    }

    @Test
    void rejectsExplicitNullExplorationMode() {
        FuzzRequestDto request = new FuzzRequestDto();
        request.setExplorationMode(null);

        assertTrue(hasProperty(validator.validate(request), "explorationMode"));
    }

    @Test
    void rejectsBudgetsAboveTheMvpResourceCaps() {
        FuzzRequestDto request = new FuzzRequestDto();
        request.setMaxIterations(5_001);
        request.setPathLength(51);
        request.setPopulationSize(51);

        Set<ConstraintViolation<FuzzRequestDto>> violations = validator.validate(request);

        assertTrue(hasProperty(violations, "maxIterations"));
        assertTrue(hasProperty(violations, "pathLength"));
        assertTrue(hasProperty(violations, "populationSize"));
    }

    @Test
    void rejectsSeedsOutsideJavaScriptSafeIntegerRange() {
        FuzzRequestDto negative = new FuzzRequestDto();
        negative.setSeed(-1L);
        FuzzRequestDto tooLarge = new FuzzRequestDto();
        tooLarge.setSeed(FuzzRequestDto.JS_SAFE_SEED_MAX + 1);

        assertFalse(validator.validate(negative).isEmpty());
        assertFalse(validator.validate(tooLarge).isEmpty());
    }

    @Test
    void rejectsBlankTargetSpecificationIds() {
        FuzzRequestDto request = new FuzzRequestDto();
        request.setTargetSpecIds(List.of("spec-1", " "));

        assertTrue(validator.validate(request).stream()
                .anyMatch(violation -> violation.getMessage().contains("cannot be blank")));
    }

    private boolean hasProperty(Set<ConstraintViolation<FuzzRequestDto>> violations, String property) {
        return violations.stream().anyMatch(violation -> violation.getPropertyPath().toString().equals(property));
    }
}
