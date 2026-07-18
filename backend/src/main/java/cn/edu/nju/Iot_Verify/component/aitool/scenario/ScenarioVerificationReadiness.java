package cn.edu.nju.Iot_Verify.component.aitool.scenario;

import com.fasterxml.jackson.databind.JsonNode;

import java.util.ArrayList;
import java.util.List;

/** Reports whether a scene can be submitted to the current verification entry points. */
public final class ScenarioVerificationReadiness {

    private ScenarioVerificationReadiness() {
    }

    public static Status assess(JsonNode scene) {
        List<Issue> issues = new ArrayList<>();
        if (scene == null || !scene.path("devices").isArray() || scene.path("devices").isEmpty()) {
            issues.add(new Issue("NO_DEVICES", "Add at least one device before verification."));
        }
        if (scene == null || !scene.path("specs").isArray() || scene.path("specs").isEmpty()) {
            issues.add(new Issue("NO_SPECIFICATIONS", "Add at least one valid specification before verification."));
        }
        return new Status(issues.isEmpty(), List.copyOf(issues));
    }

    public record Status(boolean verificationReady, List<Issue> readinessIssues) {
    }

    public record Issue(String code, String message) {
    }
}
