package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;

import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.TreeSet;

/** Canonical signature for the authored inputs from which a specification is rebuilt. */
public final class SpecificationSemanticSignature {

    private SpecificationSemanticSignature() {
    }

    public record Signature(
            String templateId,
            Set<String> aConditions,
            Set<String> ifConditions,
            Set<String> thenConditions
    ) {
    }

    public static Signature from(SpecificationDto specification) {
        if (specification == null) {
            return new Signature("", Set.of(), Set.of(), Set.of());
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

    private static Set<String> conditionKeys(List<SpecConditionDto> conditions) {
        Set<String> keys = new TreeSet<>();
        if (conditions == null) {
            return keys;
        }
        for (SpecConditionDto condition : conditions) {
            if (condition == null) {
                continue;
            }
            String targetType = normalize(condition.getTargetType()).toLowerCase(Locale.ROOT);
            String relation = normalizeRelation(condition.getRelation());
            keys.add(String.join("|",
                    normalize(condition.getDeviceId()),
                    targetType,
                    normalize(condition.getPropertyScope()).toLowerCase(Locale.ROOT),
                    normalize(condition.getKey()),
                    relation,
                    normalizeValue(condition.getValue(), relation, targetType)));
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
