package cn.edu.nju.Iot_Verify.dto.recommendation;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class RecommendationDtoSerializationTest {

    private final ObjectMapper objectMapper = new ObjectMapper();

    @Test
    void deviceRecommendation_doesNotTurnOmittedRuntimeIntoExplicitNullOverrides() throws Exception {
        DeviceRecommendationDto dto = objectMapper.convertValue(Map.of(
                "templateName", "DoorSensor",
                "suggestedLabel", "Front door sensor",
                "initialVariables", List.of(Map.of("name", "battery", "value", "90"))
        ), DeviceRecommendationDto.class);

        JsonNode json = objectMapper.valueToTree(dto);

        assertFalse(json.has("initialState"));
        assertFalse(json.has("currentStateTrust"));
        assertFalse(json.has("currentStatePrivacy"));
        assertFalse(json.path("initialVariables").get(0).has("trust"));
    }

    @Test
    void ruleRecommendation_omitsInapplicableApiAndContentFields() {
        RuleRecommendationDto dto = objectMapper.convertValue(Map.of(
                "name", "Alert on motion",
                "conditions", List.of(Map.of(
                        "deviceId", "device-1",
                        "deviceLabel", "Hall sensor",
                        "deviceName", "Hall sensor",
                        "attribute", "motion",
                        "targetType", "api")),
                "command", Map.of(
                        "deviceId", "device-2",
                        "deviceLabel", "Alarm",
                        "deviceName", "Alarm",
                        "action", "turnOn")
        ), RuleRecommendationDto.class);

        JsonNode json = objectMapper.valueToTree(dto);

        assertFalse(json.path("conditions").get(0).has("relation"));
        assertFalse(json.path("conditions").get(0).has("value"));
        assertFalse(json.path("command").has("contentDevice"));
        assertFalse(json.path("command").has("content"));
    }

    @Test
    void specificationRecommendation_usesOnlyAuthoredSemanticConditionFields() {
        SpecificationRecommendationDto dto = objectMapper.convertValue(Map.of(
                "rationale", "Check the front door",
                "templateId", "3",
                "aConditions", List.of(Map.of(
                        "deviceId", "device-1",
                        "deviceLabel", "Front door",
                        "targetType", "state",
                        "key", "state",
                        "relation", "=",
                        "value", "open")),
                "ifConditions", List.of(),
                "thenConditions", List.of()
        ), SpecificationRecommendationDto.class);

        JsonNode condition = objectMapper.valueToTree(dto).path("aConditions").get(0);

        assertEquals("device-1", condition.path("deviceId").asText());
        assertTrue(condition.has("deviceLabel"));
        assertFalse(condition.has("id"));
        assertFalse(condition.has("side"));
        assertFalse(condition.has("propertyScope"));
    }
}
