package cn.edu.nju.Iot_Verify.component.aitool.scenario;

/** Explicit minimum item counts that define completion for a scenario recommendation. */
public record ScenarioObjectiveTargets(int minDevices, int minRules, int minSpecs) {

    public static final int MIN_COUNT = 1;
    public static final int MAX_COUNT = 10;

    public ScenarioObjectiveTargets {
        requireSupportedCount(minDevices, "minDevices");
        requireSupportedCount(minRules, "minRules");
        requireSupportedCount(minSpecs, "minSpecs");
    }

    public static ScenarioObjectiveTargets baseline() {
        return new ScenarioObjectiveTargets(1, 1, 1);
    }

    public int requestedCount() {
        return minDevices + minRules + minSpecs;
    }

    private static void requireSupportedCount(int value, String field) {
        if (value < MIN_COUNT || value > MAX_COUNT) {
            throw new IllegalArgumentException(
                    field + " must be between " + MIN_COUNT + " and " + MAX_COUNT);
        }
    }
}
