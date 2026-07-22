package cn.edu.nju.Iot_Verify.component.aitool.scenario;

import com.fasterxml.jackson.databind.JsonNode;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/** Reports whether a scene can be submitted to the current verification entry points. */
public final class ScenarioVerificationReadiness {

    private ScenarioVerificationReadiness() {
    }

    public static Status assess(JsonNode scene) {
        return assess(scene, 0, "en");
    }

    public static Status assess(JsonNode scene, int filteredCount, String language) {
        List<Issue> issues = new ArrayList<>();
        if (scene == null || !scene.path("devices").isArray() || scene.path("devices").isEmpty()) {
            issues.add(new Issue("NO_DEVICES", "Add at least one device before verification."));
        }
        if (scene == null || !scene.path("specs").isArray() || scene.path("specs").isEmpty()) {
            issues.add(new Issue("NO_SPECIFICATIONS", "Add at least one valid specification before verification."));
        }
        return new Status(
                issues.isEmpty(),
                List.copyOf(issues),
                semanticWarnings(scene, Math.max(0, filteredCount), "zh-CN".equals(language)));
    }

    private static List<Issue> semanticWarnings(JsonNode scene, int filteredCount, boolean chinese) {
        List<Issue> warnings = new ArrayList<>();
        if (filteredCount > 0) {
            warnings.add(new Issue(
                    "FILTERED_CANDIDATES",
                    chinese
                            ? String.format("有 %d 个生成候选未通过校验。最终草案可能不再覆盖生成设计或用户需求的全部内容。", filteredCount)
                            : String.format("%d generated candidate(s) failed validation. The final draft may no longer cover every part of the generated design or user requirement.", filteredCount)));
        }
        if (scene == null || !scene.path("devices").isArray() || scene.path("devices").isEmpty()) {
            return List.copyOf(warnings);
        }

        JsonNode rules = scene.path("rules");
        if (!rules.isArray() || rules.isEmpty()) {
            warnings.add(new Issue(
                    "NO_AUTOMATION_RULES",
                    chinese
                            ? "最终草案不包含保留的自动化规则。它仍可包含规约，但不能据此宣称已形成自动化闭环。"
                            : "The final draft contains no retained automation rules. It may still contain specifications, but it does not establish an automation closed loop."));
        }

        Set<String> referencedDeviceIds = referencedDeviceIds(scene);
        List<String> unreferencedLabels = new ArrayList<>();
        for (JsonNode device : scene.path("devices")) {
            String id = device.path("id").asText("").trim();
            if (id.isEmpty() || referencedDeviceIds.contains(id)) {
                continue;
            }
            String label = device.path("label").asText("").trim();
            unreferencedLabels.add(label.isEmpty() ? id : label);
        }
        if (!unreferencedLabels.isEmpty()) {
            String labels = String.join(", ", unreferencedLabels);
            warnings.add(new Issue(
                    "UNREFERENCED_DEVICES",
                    chinese
                            ? String.format("有 %d 个保留设备未被任何保留规则或规约引用：%s。它们可能是有意独立存在，但草案未证明其参与了用户要求的行为。", unreferencedLabels.size(), labels)
                            : String.format("%d retained device(s) are not referenced by any retained rule or specification: %s. They may be intentionally independent, but the draft does not establish their role in the requested behavior.", unreferencedLabels.size(), labels)));
        }
        return List.copyOf(warnings);
    }

    private static Set<String> referencedDeviceIds(JsonNode scene) {
        Set<String> references = new LinkedHashSet<>();
        JsonNode rules = scene.path("rules");
        if (rules.isArray()) {
            for (JsonNode rule : rules) {
                collectText(references, rule, "toId");
                collectText(references, rule, "contentDevice");
                JsonNode sources = rule.path("sources");
                if (sources.isArray()) {
                    for (JsonNode source : sources) {
                        collectText(references, source, "fromId");
                    }
                }
            }
        }
        JsonNode specs = scene.path("specs");
        if (specs.isArray()) {
            for (JsonNode spec : specs) {
                collectConditionDeviceIds(references, spec.path("aConditions"));
                collectConditionDeviceIds(references, spec.path("ifConditions"));
                collectConditionDeviceIds(references, spec.path("thenConditions"));
            }
        }
        return references;
    }

    private static void collectConditionDeviceIds(Set<String> references, JsonNode conditions) {
        if (!conditions.isArray()) {
            return;
        }
        for (JsonNode condition : conditions) {
            collectText(references, condition, "deviceId");
        }
    }

    private static void collectText(Set<String> values, JsonNode node, String field) {
        String value = node.path(field).asText("").trim();
        if (!value.isEmpty()) {
            values.add(value);
        }
    }

    public record Status(
            boolean verificationReady,
            List<Issue> readinessIssues,
            List<Issue> semanticWarnings) {
    }

    public record Issue(String code, String message) {
    }
}
