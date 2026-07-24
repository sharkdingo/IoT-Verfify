package cn.edu.nju.Iot_Verify.component.aitool.scenario;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ScenarioVerificationReadinessTest {

    private final ObjectMapper objectMapper = new ObjectMapper();

    @Test
    void assess_keepsStructuralReadinessSeparateFromSemanticCoverage() throws Exception {
        JsonNode scene = objectMapper.readTree("""
                {
                  "devices": [
                    {"id":"device_1","label":"Hall sensor"},
                    {"id":"device_2","label":"Emergency siren"}
                  ],
                  "rules": [],
                  "specs": [
                    {
                      "aConditions":[{"deviceId":"device_1"}],
                      "ifConditions":[],
                      "thenConditions":[]
                    }
                  ]
                }
                """);

        ScenarioVerificationReadiness.Status status =
                ScenarioVerificationReadiness.assess(scene, 1, "en");

        assertEquals("PARTIAL", status.objectiveStatus());
        assertEquals(List.of("NO_AUTOMATION_RULES"), status.objectiveIssues().stream()
                .map(ScenarioVerificationReadiness.Issue::code)
                .toList());
        assertTrue(status.verificationReady());
        assertTrue(status.readinessIssues().isEmpty());
        assertEquals(
                List.of("FILTERED_CANDIDATES", "NO_AUTOMATION_RULES", "UNREFERENCED_DEVICES"),
                status.semanticWarnings().stream()
                        .map(ScenarioVerificationReadiness.Issue::code)
                        .toList());
        assertTrue(status.semanticWarnings().get(2).message().contains("Emergency siren"));
    }

    @Test
    void assess_marksPositiveCountsBelowExplicitTargetsAsPartial() throws Exception {
        JsonNode scene = objectMapper.readTree("""
                {
                  "devices":[{"id":"device_1"},{"id":"device_2"}],
                  "rules":[{"toId":"device_2","sources":[]}],
                  "specs":[{},{}]
                }
                """);

        ScenarioVerificationReadiness.Status status = ScenarioVerificationReadiness.assess(
                scene,
                0,
                "en",
                new ScenarioObjectiveTargets(3, 2, 2));

        assertEquals("PARTIAL", status.objectiveStatus());
        assertEquals(
                List.of("INSUFFICIENT_DEVICES", "INSUFFICIENT_AUTOMATION_RULES"),
                status.objectiveIssues().stream().map(ScenarioVerificationReadiness.Issue::code).toList());
        assertTrue(status.objectiveIssues().get(0).message().contains("explicit minimum of 3"));
        assertTrue(status.verificationReady());
    }
}
