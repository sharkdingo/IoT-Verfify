package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;

import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.Set;
import java.util.TreeSet;

/** Canonical, order-insensitive signature for the behavior represented by a board rule. */
public final class RuleSemanticSignature {

    private RuleSemanticSignature() {
    }

    public record Signature(
            String commandKey,
            Set<String> conditionKeys,
            Set<String> conditionShapeKeys
    ) {
    }

    public static Signature from(RuleDto rule) {
        if (rule == null) {
            return new Signature("", Set.of(), Set.of());
        }
        return new Signature(
                commandKey(rule.getCommand()),
                canonicalConditionKeys(rule.getConditions(), false),
                canonicalConditionKeys(rule.getConditions(), true));
    }

    public static boolean exactlyMatches(RuleDto left, RuleDto right) {
        Signature leftSignature = from(left);
        Signature rightSignature = from(right);
        return leftSignature.commandKey().equals(rightSignature.commandKey())
                && leftSignature.conditionKeys().equals(rightSignature.conditionKeys());
    }

    private static String commandKey(RuleDto.Command command) {
        if (command == null) {
            return "";
        }
        return String.join("|",
                normalize(command.getDeviceName()),
                normalize(command.getAction()),
                normalize(command.getContentDevice()),
                normalize(command.getContent()));
    }

    private static Set<String> canonicalConditionKeys(List<RuleDto.Condition> conditions, boolean shapeOnly) {
        Set<String> result = new TreeSet<>();
        if (conditions == null) {
            return result;
        }
        for (RuleDto.Condition condition : conditions) {
            if (condition == null) {
                continue;
            }
            String targetType = normalize(condition.getTargetType()).toLowerCase(Locale.ROOT);
            String relation = "api".equals(targetType) ? "" : normalizeRelation(condition.getRelation());
            String value = shapeOnly || "api".equals(targetType)
                    ? ""
                    : normalizeConditionValue(condition.getValue(), relation, targetType);
            result.add(String.join("|",
                    normalize(condition.getDeviceName()),
                    targetType,
                    normalize(condition.getAttribute()),
                    relation,
                    value));
        }
        return result;
    }

    private static String normalizeConditionValue(String value, String relation, String targetType) {
        String normalized = normalize(value);
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
