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
}
