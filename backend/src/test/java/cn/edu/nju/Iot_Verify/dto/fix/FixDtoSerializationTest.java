package cn.edu.nju.Iot_Verify.dto.fix;

import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.JsonNode;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class FixDtoSerializationTest {

    private final ObjectMapper objectMapper = new ObjectMapper();

    @Test
    void externalFixDtosHideInternalRuleAndConditionLocators() throws Exception {
        ParameterAdjustment parameter = ParameterAdjustment.builder()
                .targetId("param_abcdefghijklmnopqrstuvwx")
                .ruleIndex(3)
                .conditionIndex(4)
                .attribute("temperature")
                .relation(">")
                .originalValue("30")
                .newValue("25")
                .lowerBound(0)
                .upperBound(50)
                .description("Adjust the kitchen temperature threshold")
                .build();
        ConditionAdjustment condition = ConditionAdjustment.builder()
                .ruleIndex(5)
                .conditionIndex(6)
                .action("remove")
                .attribute("motion")
                .deviceName("kitchen_motion_1")
                .deviceLabel("Kitchen motion sensor")
                .description("Remove the conflicting motion condition")
                .build();
        FaultRuleDto faultRule = FaultRuleDto.builder()
                .ruleIndex(7)
                .ruleId(42L)
                .conflictWithRuleIndex(8)
                .targetDeviceId("kitchen_light_17")
                .targetActionId("turnOn")
                .targetDeviceLabel("Kitchen light")
                .targetActionLabel("Turn on")
                .transitionNumber(1)
                .ruleString("IF kitchen.motion = active THEN kitchen.light.turnOn")
                .build();
        FixSuggestionDto suggestion = FixSuggestionDto.builder()
                .strategy("remove")
                .parameterAdjustments(List.of(parameter))
                .conditionAdjustments(List.of(condition))
                .removedRuleIndices(List.of(9))
                .removedRuleDescriptions(List.of("IF kitchen.motion = active THEN kitchen.light.turnOn"))
                .verified(true)
                .build();

        String json = objectMapper.writeValueAsString(FixResultDto.builder()
                .faultRules(List.of(faultRule))
                .suggestions(List.of(suggestion))
                .build());

        assertFalse(json.contains("ruleIndex"));
        assertFalse(json.contains("conditionIndex"));
        assertFalse(json.contains("conflictWithRuleIndex"));
        assertFalse(json.contains("ruleId"));
        assertFalse(json.contains("targetDeviceId"));
        assertFalse(json.contains("targetActionId"));
        assertFalse(json.contains("kitchen_motion_1"));
        assertFalse(json.contains("removedRuleIndices"));
        assertTrue(json.contains("Kitchen motion sensor"));
        assertTrue(json.contains("Kitchen light"));
        assertTrue(json.contains("removedRuleDescriptions"));
        assertTrue(json.contains("Adjust the kitchen temperature threshold"));
    }

    @Test
    void nonApplicableFixCollectionsSerializeAsEmptyArrays() throws Exception {
        FixSuggestionDto suggestion = FixSuggestionDto.builder()
                .strategy("remove")
                .description("No verified removal was found")
                .verified(false)
                .build();

        JsonNode root = objectMapper.readTree(objectMapper.writeValueAsString(
                FixResultDto.builder().suggestions(List.of(suggestion)).build()));
        JsonNode suggestionJson = root.path("suggestions").path(0);

        assertEquals(0, suggestionJson.path("parameterAdjustments").size());
        assertEquals(0, suggestionJson.path("conditionAdjustments").size());
        assertEquals(0, suggestionJson.path("removedRuleDescriptions").size());
        assertEquals(0, root.path("faultRules").size());
        assertEquals(0, root.path("strategyAttempts").size());
        assertEquals("NOT_CHECKED", root.path("templateSnapshotComparison").asText());
        assertEquals(0, root.path("warnings").size());
        assertEquals(0, root.path("unusedPreferredRangeSelections").size());
    }
}
