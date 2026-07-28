package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;

import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.TreeMap;

/** Canonical signature for the authored inputs from which a specification is rebuilt. */
public final class SpecificationSemanticSignature {

    private SpecificationSemanticSignature() {
    }

    public record Signature(
            String templateId,
            Map<String, Long> aConditions,
            Map<String, Long> ifConditions,
            Map<String, Long> thenConditions
    ) {
    }

    public static Signature from(SpecificationDto specification) {
        if (specification == null) {
            return new Signature("", Map.of(), Map.of(), Map.of());
        }
        return new Signature(
                normalize(specification.getTemplateId()),
                conditionKeys(specification.getAConditions()),
                conditionKeys(specification.getIfConditions()),
                conditionKeys(specification.getThenConditions()));
    }

    public static boolean exactlyMatches(SpecificationDto left, SpecificationDto right) {
        return from(left).equals(from(right));
    }

    /**
     * Canonical condition keys with their occurrence counts.
     *
     * <p>A multiset rather than a set: cardinality is part of a specification's identity, and this
     * signature gates the "delete only if unchanged" and duplicate-spec checks. Collapsing a
     * repeated condition let a delete land on a specification that had genuinely been edited.
     */
    private static Map<String, Long> conditionKeys(List<SpecConditionDto> conditions) {
        Map<String, Long> keys = new TreeMap<>();
        if (conditions == null) {
            return keys;
        }
        for (SpecConditionDto condition : conditions) {
            if (condition == null) {
                continue;
            }
            String targetType = normalize(condition.getTargetType()).toLowerCase(Locale.ROOT);
            String relation = normalizeRelation(condition.getRelation());
            keys.merge(String.join("|",
                    normalize(condition.getDeviceId()),
                    targetType,
                    normalize(condition.getPropertyScope()).toLowerCase(Locale.ROOT),
                    normalize(condition.getKey()),
                    relation,
                    normalizeValue(condition.getValue(), relation, targetType)), 1L, Long::sum);
        }
        return keys;
    }

    private static String normalizeValue(String value, String relation, String targetType) {
        String normalized = normalize(value);
        if ("api".equals(targetType)) {
            return normalized.toUpperCase(Locale.ROOT);
        }
        if (!"in".equals(relation) && !"not in".equals(relation)) {
            return normalized;
        }
        String delimiter = "state".equals(targetType) ? "[,|]" : "[,;|]";
        return Arrays.stream(normalized.split(delimiter))
                .map(String::trim)
                .filter(part -> !part.isBlank())
                .sorted()
                .reduce((left, right) -> left + "," + right)
                .orElse("");
    }

    private static String normalizeRelation(String relation) {
        String value = normalize(relation);
        return switch (value.toUpperCase(Locale.ROOT)) {
            case "EQ", "==" -> "=";
            case "NEQ" -> "!=";
            case "GT" -> ">";
            case "GTE" -> ">=";
            case "LT" -> "<";
            case "LTE" -> "<=";
            case "IN" -> "in";
            case "NOT_IN", "NOT IN" -> "not in";
            default -> value;
        };
    }

    private static String normalize(String value) {
        return value == null ? "" : value.trim();
    }
}
