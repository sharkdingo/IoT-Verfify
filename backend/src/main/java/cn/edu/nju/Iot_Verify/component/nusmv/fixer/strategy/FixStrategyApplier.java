package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.fix.ConditionAdjustment;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.fix.ParameterAdjustment;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import lombok.extern.slf4j.Slf4j;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Applies a verified {@link FixSuggestionDto} onto a set of rules, producing the modified rule list.
 *
 * <p>This mirrors the mutation semantics each fix strategy uses internally when it forward-verifies a
 * candidate, but operates on the caller's rule list (the persisted board rules) so the change can be
 * saved. It is intentionally strategy-agnostic and pure (no NuSMV, no persistence).</p>
 *
 * <p>Lives in the strategy package to reuse the package-private helpers in {@link FixStrategyUtils}
 * (device varName resolution and condition fingerprinting).</p>
 */
@Slf4j
public final class FixStrategyApplier {

    private FixStrategyApplier() {}

    /**
     * Apply the suggestion to a deep copy of {@code rules} and return the modified list.
     * The input list is not mutated.
     */
    public static List<RuleDto> apply(String strategy, FixSuggestionDto suggestion,
                                      List<RuleDto> rules, Map<String, DeviceSmvData> deviceSmvMap) {
        return apply(strategy, suggestion, rules, deviceSmvMap, Map.of());
    }

    /**
     * Apply the suggestion, translating newly-added condition device references through
     * {@code persistenceDeviceNames} when provided. Verified suggestions are computed against SMV
     * varNames, while persisted rules should keep the board's current device labels so the UI can
     * resolve them directly.
     */
    public static List<RuleDto> apply(String strategy, FixSuggestionDto suggestion,
                                      List<RuleDto> rules, Map<String, DeviceSmvData> deviceSmvMap,
                                      Map<String, String> persistenceDeviceNames) {
        List<RuleDto> working = FixStrategyUtils.deepCopyRules(rules);
        switch (strategy) {
            case "parameter":
                applyParameter(suggestion.getParameterAdjustments(), working);
                return working;
            case "condition":
                return applyCondition(suggestion.getConditionAdjustments(), working, persistenceDeviceNames);
            case "disable":
                return applyDisable(suggestion.getDisabledRuleIndices(), working);
            default:
                throw new BadRequestException("Unsupported fix strategy: " + strategy);
        }
    }

    // ---- parameter: overwrite the threshold value of an existing condition ----

    private static void applyParameter(List<ParameterAdjustment> adjustments, List<RuleDto> rules) {
        if (adjustments == null || adjustments.isEmpty()) {
            throw new BadRequestException("Parameter fix has no adjustments to apply.");
        }
        for (ParameterAdjustment adj : adjustments) {
            RuleDto.Condition cond = conditionAt(rules, adj.getRuleIndex(), adj.getConditionIndex());
            // Sanity check: the condition we are about to edit should be the one the fix targeted.
            if (adj.getAttribute() != null && cond.getAttribute() != null
                    && !adj.getAttribute().equals(cond.getAttribute())) {
                throw new BadRequestException("Parameter fix target mismatch at rule "
                        + adj.getRuleIndex() + " condition " + adj.getConditionIndex()
                        + ": expected attribute '" + adj.getAttribute()
                        + "' but found '" + cond.getAttribute() + "'.");
            }
            cond.setValue(adj.getNewValue());
            if (adj.getRelation() != null && !adj.getRelation().isBlank()) {
                cond.setRelation(adj.getRelation());
            }
        }
    }

    // ---- condition: add candidate conditions and remove disabled ones ----

    private static List<RuleDto> applyCondition(List<ConditionAdjustment> adjustments, List<RuleDto> rules,
                                                Map<String, String> persistenceDeviceNames) {
        if (adjustments == null || adjustments.isEmpty()) {
            throw new BadRequestException("Condition fix has no adjustments to apply.");
        }
        // Group by rule so we can remove by descending index safely and add afterwards.
        Map<Integer, List<Integer>> toRemove = new LinkedHashMap<>();
        Map<Integer, List<RuleDto.Condition>> toAdd = new LinkedHashMap<>();

        for (ConditionAdjustment adj : adjustments) {
            String action = adj.getAction();
            if (action == null || "keep".equals(action)) continue;
            int ruleIdx = adj.getRuleIndex();
            requireRuleIndex(rules, ruleIdx);
            if ("remove".equals(action)) {
                toRemove.computeIfAbsent(ruleIdx, k -> new ArrayList<>()).add(adj.getConditionIndex());
            } else if ("add".equals(action)) {
                RuleDto.Condition cond = RuleDto.Condition.builder()
                        .deviceName(persistenceDeviceName(adj.getDeviceName(), persistenceDeviceNames))
                        .attribute(adj.getAttribute())
                        .relation(adj.getRelation())
                        .value(adj.getValue())
                        .build();
                toAdd.computeIfAbsent(ruleIdx, k -> new ArrayList<>()).add(cond);
            } else {
                throw new BadRequestException("Unknown condition action: " + action);
            }
        }

        // 1) remove existing conditions in descending index order to keep indices valid
        for (Map.Entry<Integer, List<Integer>> e : toRemove.entrySet()) {
            List<Integer> indices = new ArrayList<>(e.getValue());
            indices.sort(Collections.reverseOrder());
            List<RuleDto.Condition> conds = rules.get(e.getKey()).getConditions();
            if (conds == null) continue;
            for (int idx : indices) {
                if (idx >= 0 && idx < conds.size()) {
                    conds.remove(idx);
                }
            }
        }
        // 2) add candidate conditions
        for (Map.Entry<Integer, List<RuleDto.Condition>> e : toAdd.entrySet()) {
            RuleDto rule = rules.get(e.getKey());
            if (rule.getConditions() == null) {
                rule.setConditions(new ArrayList<>());
            }
            rule.getConditions().addAll(e.getValue());
        }

        // A rule with no conditions left would be an always-on trigger; reject rather than persist that.
        for (RuleDto rule : rules) {
            if (rule.getConditions() == null || rule.getConditions().isEmpty()) {
                throw new BadRequestException("Applying this condition fix would leave a rule with no "
                        + "trigger conditions. Please review the suggestion manually.");
            }
        }
        return rules;
    }

    private static String persistenceDeviceName(String deviceName, Map<String, String> persistenceDeviceNames) {
        if (deviceName == null || persistenceDeviceNames == null || persistenceDeviceNames.isEmpty()) {
            return deviceName;
        }
        String mapped = persistenceDeviceNames.get(deviceName);
        return mapped != null ? mapped : deviceName;
    }

    // ---- disable: drop the flagged rules entirely ----

    private static List<RuleDto> applyDisable(List<Integer> disabledIndices, List<RuleDto> rules) {
        if (disabledIndices == null || disabledIndices.isEmpty()) {
            throw new BadRequestException("Disable fix has no rule indices to remove.");
        }
        for (int idx : disabledIndices) {
            requireRuleIndex(rules, idx);
        }
        List<RuleDto> remaining = new ArrayList<>();
        for (int i = 0; i < rules.size(); i++) {
            if (!disabledIndices.contains(i)) {
                remaining.add(rules.get(i));
            }
        }
        return remaining;
    }

    // ---- shared helpers ----

    private static RuleDto.Condition conditionAt(List<RuleDto> rules, int ruleIdx, int condIdx) {
        requireRuleIndex(rules, ruleIdx);
        List<RuleDto.Condition> conds = rules.get(ruleIdx).getConditions();
        if (conds == null || condIdx < 0 || condIdx >= conds.size()) {
            throw new BadRequestException("Fix references condition " + condIdx + " of rule " + ruleIdx
                    + " which does not exist.");
        }
        return conds.get(condIdx);
    }

    private static void requireRuleIndex(List<RuleDto> rules, int ruleIdx) {
        if (ruleIdx < 0 || ruleIdx >= rules.size()) {
            throw new BadRequestException("Fix references rule index " + ruleIdx
                    + " which is out of range (0.." + (rules.size() - 1) + ").");
        }
    }

    /** Expose {@link FixStrategyUtils#resolveVarNameSafe} for the service's drift check. */
    public static String resolveVarName(String deviceName, Map<String, DeviceSmvData> deviceSmvMap) {
        String v = FixStrategyUtils.resolveVarNameSafe(deviceName, deviceSmvMap);
        return v != null ? v : (deviceName == null ? "" : deviceName);
    }

    /** Expose {@link FixStrategyUtils#conditionFingerprint} for the service's drift check. */
    public static String conditionFingerprint(RuleDto.Condition c, Map<String, DeviceSmvData> deviceSmvMap) {
        String fp = FixStrategyUtils.conditionFingerprint(c, deviceSmvMap);
        return fp != null ? fp : "?";
    }
}
