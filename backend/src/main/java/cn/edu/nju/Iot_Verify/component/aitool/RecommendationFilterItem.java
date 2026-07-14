package cn.edu.nju.Iot_Verify.component.aitool;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * User-facing metadata for an AI recommendation candidate discarded during backend validation.
 */
public record RecommendationFilterItem(
        String type,
        int index,
        String reasonCode,
        String reason,
        String label
) {
    public Map<String, Object> toMap() {
        Map<String, Object> row = new LinkedHashMap<>();
        row.put("type", type);
        row.put("index", index);
        row.put("reasonCode", reasonCode);
        row.put("reason", reason);
        if (label != null && !label.isBlank()) {
            row.put("label", label);
        }
        return row;
    }
}
