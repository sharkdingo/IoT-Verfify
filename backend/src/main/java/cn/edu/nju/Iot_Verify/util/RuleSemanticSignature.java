package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

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

    /**
     * True when both rules command the same thing under exactly the same conditions.
     *
     * <p>Compares condition <em>multisets</em>, not the {@link Signature} sets. Order carries no
     * meaning in a conjunction, so this stays order-insensitive — but cardinality does: a rule
     * edited from {@code [C, C]} to {@code [C]} has changed. This predicate also gates the
     * "delete only if unchanged" and undo/redo conflict checks, where treating those two as equal
     * let a delete land on a rule the user had never reviewed.
     *
     * <p>{@code Signature} keeps set semantics deliberately: its consumer reasons about subset and
     * overlap between different rules, where collapsing duplicates is correct.
     */
    public static boolean exactlyMatches(RuleDto left, RuleDto right) {
        return commandKey(left == null ? null : left.getCommand())
                .equals(commandKey(right == null ? null : right.getCommand()))
                && conditionMultiset(left).equals(conditionMultiset(right));
    }

    /** Canonical condition keys with their occurrence counts, so cardinality survives comparison. */
    private static Map<String, Long> conditionMultiset(RuleDto rule) {
        if (rule == null) {
            return Map.of();
        }
        return canonicalConditionKeyList(rule.getConditions(), false).stream()
                .collect(Collectors.groupingBy(key -> key, Collectors.counting()));
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
        return new TreeSet<>(canonicalConditionKeyList(conditions, shapeOnly));
    }

    /**
     * One canonical key per condition, duplicates retained.
     *
     * <p>The set and multiset views are both derived from this list so a normalization change cannot
     * apply to only one of them.
     */
    private static List<String> canonicalConditionKeyList(List<RuleDto.Condition> conditions, boolean shapeOnly) {
        List<String> result = new ArrayList<>();
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
