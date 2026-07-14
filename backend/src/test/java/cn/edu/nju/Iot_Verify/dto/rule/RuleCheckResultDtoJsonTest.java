package cn.edu.nju.Iot_Verify.dto.rule;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class RuleCheckResultDtoJsonTest {

    private final ObjectMapper objectMapper = new ObjectMapper();

    @Test
    void duplicateCheckUsesDocumentedBooleanFieldName() {
        DuplicateRuleCheckResultDto result = DuplicateRuleCheckResultDto.builder()
                .isDuplicate(false)
                .requiresReview(false)
                .similarity(0.0)
                .matchType("none")
                .reasonCode("NO_EXISTING_RULES")
                .reason("no existing rules")
                .message("This is the first rule.")
                .build();

        JsonNode json = objectMapper.valueToTree(result);

        assertTrue(json.has("isDuplicate"));
        assertTrue(json.has("reasonCode"));
        assertFalse(json.has("duplicate"));
    }

    @Test
    void similarityCheckUsesDocumentedBooleanFieldNames() {
        RuleSimilarityResultDto result = RuleSimilarityResultDto.builder()
                .isSimilar(false)
                .isDuplicate(false)
                .requiresReview(false)
                .similarity(0.0)
                .reasonCode("AI_NO_SIGNIFICANT_SIMILARITY")
                .reason("no semantic match")
                .message("No similar rule found.")
                .build();

        JsonNode json = objectMapper.valueToTree(result);

        assertTrue(json.has("isSimilar"));
        assertTrue(json.has("isDuplicate"));
        assertTrue(json.has("requiresReview"));
        assertTrue(json.has("reasonCode"));
        assertFalse(json.has("similar"));
        assertFalse(json.has("duplicate"));
    }
}
