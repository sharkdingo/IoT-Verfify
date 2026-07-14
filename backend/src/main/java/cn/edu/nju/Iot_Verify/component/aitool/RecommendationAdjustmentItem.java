package cn.edu.nju.Iot_Verify.component.aitool;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * User-facing metadata for deterministic values added to an AI recommendation.
 *
 * <p>Filtered items explain why a candidate was rejected. Adjustment items explain why a
 * kept candidate is not byte-for-byte identical to the raw AI output, so callers can show
 * every template or layout default before a user applies the recommendation.</p>
 */
public record RecommendationAdjustmentItem(
        String type,
        Integer index,
        String reasonCode,
        String reason,
        String label,
        Map<String, Object> appliedValues
) {
    public Map<String, Object> toMap() {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("type", type);
        if (index != null) {
            row.put("index", index);
        }
        row.put("reasonCode", reasonCode);
        row.put("reason", reason);
        if (label != null && !label.isBlank()) {
            row.put("label", label);
        }
        row.put("appliedValues", appliedValues == null
                ? Map.of()
                : new LinkedHashMap<>(appliedValues));
        return row;
    }
}
