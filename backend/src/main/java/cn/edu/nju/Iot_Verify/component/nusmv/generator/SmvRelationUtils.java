package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;

import java.util.ArrayList;
import java.util.List;

/**
 * Shared relation normalization and validation logic for SMV generation.
 * Used by SmvModelValidator, SmvMainModuleBuilder, SmvSpecificationBuilder, and FixStrategyUtils.
 */
public final class SmvRelationUtils {

    private SmvRelationUtils() {
    }

    /**
     * Normalize a trigger relation string to its canonical NuSMV form.
     * Supports: EQ/== → =, NEQ/!= → !=, GT → >, GTE → >=, LT → <, LTE → <=
     */
    public static String normalizeTriggerRelation(String relation) {
        if (relation == null) return null;
        String normalized = relation.trim();
        return switch (normalized.toUpperCase()) {
            case "EQ", "==" -> "=";
            case "NEQ", "!=" -> "!=";
            case "GT" -> ">";
            case "GTE" -> ">=";
            case "LT" -> "<";
            case "LTE" -> "<=";
            default -> normalized;
        };
    }

    /**
     * Check whether a (already-normalized) trigger relation is supported.
     */
    public static boolean isSupportedTriggerRelation(String relation) {
        return "=".equals(relation)
                || "!=".equals(relation)
                || ">".equals(relation)
                || ">=".equals(relation)
                || "<".equals(relation)
                || "<=".equals(relation);
    }

    /**
     * Normalize a rule/spec relation string, including IN/NOT_IN support.
     * Returns null for null input (consistent with normalizeTriggerRelation).
     */
    public static String normalizeRelation(String relation) {
        if (relation == null) return null;
        String normalized = relation.trim();
        return switch (normalized.toUpperCase()) {
            case "EQ", "==" -> "=";
            case "NEQ", "!=" -> "!=";
            case "GT" -> ">";
            case "GTE" -> ">=";
            case "LT" -> "<";
            case "LTE" -> "<=";
            case "IN" -> "in";
            case "NOT_IN", "NOT IN" -> "not in";
            default -> normalized;
        };
    }

    /**
     * Check whether a (already-normalized) rule/spec relation is supported.
     */
    public static boolean isSupportedRelation(String relation) {
        return "=".equals(relation)
                || "!=".equals(relation)
                || ">".equals(relation)
                || ">=".equals(relation)
                || "<".equals(relation)
                || "<=".equals(relation)
                || "in".equals(relation)
                || "not in".equals(relation);
    }

    /**
     * Split value by ,;| delimiters for IN/NOT_IN; for other relations return the value as single-element list.
     * <p><b>Note:</b> For multi-mode devices where `;` is used inside tuple values (e.g. "cool;off"),
     * use {@link #splitStateRuleValues(String, int)} instead to avoid splitting within tuples.</p>
     */
    public static List<String> splitRuleValues(String value) {
        if (value == null) return List.of();
        String[] parts = value.split("[,;|]");
        List<String> result = new ArrayList<>();
        for (String p : parts) {
            String trimmed = p.trim();
            if (!trimmed.isEmpty()) {
                result.add(trimmed);
            }
        }
        return result;
    }

    /**
     * Mode-aware split for state IN/NOT_IN values.
     * Multi-mode devices (modeCount &gt; 1) use `;` within tuple values (e.g. "cool;off"),
     * so only split by [,|]. Single-mode devices split by [,;|].
     * Matches SmvMainModuleBuilder.splitStateRuleCandidates() semantics.
     */
    public static List<String> splitStateRuleValues(String value, int modeCount) {
        if (value == null) return List.of();
        String splitRegex = (modeCount > 1) ? "[,|]" : "[,;|]";
        String[] parts = value.split(splitRegex);
        List<String> result = new ArrayList<>();
        for (String p : parts) {
            String trimmed = p.trim();
            if (!trimmed.isEmpty()) {
                result.add(trimmed);
            }
        }
        return result;
    }

    /**
     * Clean state value via cleanStateName; for IN/NOT_IN, clean each segment individually.
     * Matches the normalization semantics used by SmvMainModuleBuilder during SMV generation.
     */
    public static String cleanRuleValueByRelation(String normalizedRelation, String value) {
        return cleanRuleValueByRelation(normalizedRelation, value, 1);
    }

    /**
     * Mode-aware variant: for IN/NOT_IN with multi-mode devices, splits by [,|] only
     * (preserving ; within tuple values). For single-mode or non-IN relations, behaves identically.
     */
    public static String cleanRuleValueByRelation(String normalizedRelation, String value, int modeCount) {
        if (value == null) return null;
        if ("in".equals(normalizedRelation) || "not in".equals(normalizedRelation)) {
            List<String> parts = splitStateRuleValues(value, modeCount);
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < parts.size(); i++) {
                if (i > 0) sb.append(",");
                sb.append(DeviceSmvDataFactory.cleanStateName(parts.get(i)));
            }
            return sb.toString();
        }
        return DeviceSmvDataFactory.cleanStateName(value);
    }
}
