package cn.edu.nju.Iot_Verify.component.nusmv.generator;

/**
 * Shared relation normalization and validation logic for SMV generation.
 * Used by SmvModelValidator, SmvMainModuleBuilder, and SmvSpecificationBuilder.
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
     */
    public static String normalizeRelation(String relation) {
        if (relation == null) return "=";
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
}
