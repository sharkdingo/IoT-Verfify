package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixContext;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixStrategy;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize.ParameterizationConfig;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize.ParameterExtractor;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceReferenceResolver;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.fix.ConditionAdjustment;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.io.File;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * §5.2 Triggering Condition Adjustment (Salus paper).
 *
 * <p>For each sub-condition in expanded rules, introduces a boolean FROZENVAR lambda.
 * Existing conditions: lambda=TRUE → keep, lambda=FALSE → remove.
 * Candidate conditions (from violated spec): lambda=TRUE → add, lambda=FALSE → ignore.
 * NuSMV solves for which conditions to remove/add.</p>
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class ConditionAdjustStrategy implements FixStrategy {

    private static final String NAME = "condition";
    private static final Pattern KEY_PATTERN = Pattern.compile("r(\\d+)_c(\\d+)");

    private final SmvGenerator smvGenerator;
    private final NusmvExecutor nusmvExecutor;
    private final FixConfig fixConfig;

    @Override
    public String name() {
        return NAME;
    }

    @Override
    public FixSuggestionDto tryFix(FixContext ctx) {
        List<FaultRuleDto> faultRules = ctx.getFaultRules();
        List<RuleDto> allRules = ctx.getAllRules();
        int violatedSpecIndex = ctx.getViolatedSpecIndex();
        int maxAttempts = ctx.getMaxAttempts() > 0 ? ctx.getMaxAttempts() : 20;

        if (faultRules == null || faultRules.isEmpty()) return null;

        // §5: Expand scope + prepare augmented rules with candidate conditions
        SpecificationDto violatedSpec = ctx.getSpecs().get(violatedSpecIndex);
        Map<String, DeviceSmvData> deviceSmvMap = ctx.getDeviceSmvMap();
        Set<Integer> expandedIndices = FixStrategyUtils.expandRuleIndices(
                faultRules, allRules, violatedSpec, deviceSmvMap);

        PreparedData prep = prepareAugmentedRules(allRules, expandedIndices, violatedSpec, deviceSmvMap);
        if (prep == null) return null;

        log.info("ConditionAdjustStrategy: created {} lambda variable(s)", prep.conditionLambdas.size());

        // Solve loop
        List<String> exclusionInvars = new ArrayList<>();
        Set<Integer> partialOutputHashes = new HashSet<>();
        int consecutivePartials = 0;

        for (int attempt = 0; attempt < maxAttempts; attempt++) {
            if (ctx.isExpired()) {
                log.info("ConditionAdjustStrategy: deadline expired at attempt {}/{}", attempt + 1, maxAttempts);
                break;
            }
            ParameterizationConfig config = ParameterizationConfig.builder()
                    .conditionLambdas(prep.conditionLambdas)
                    .negatedSpecIndex(violatedSpecIndex)
                    .exclusionInvars(exclusionInvars.isEmpty() ? null : new ArrayList<>(exclusionInvars))
                    .build();

            File smvFile = null;
            try {
                // Pass augmentedRules (with candidate conditions appended) to NuSMV
                SmvGenerator.GenerateResult genResult =
                        FixStrategyUtils.generateParameterizedResolved(
                                smvGenerator, ctx, prep.augmentedRules, config);
                if (genResult == null) {
                    log.warn("ConditionAdjust attempt {}: SMV generation returned null", attempt + 1);
                    continue;
                }
                smvFile = genResult.smvFile();

                NusmvResult result = FixStrategyUtils.executeWithinDeadline(nusmvExecutor, smvFile, ctx);
                if (!result.isSuccess()) {
                    log.warn("ConditionAdjust attempt {}: NuSMV execution failed: {}",
                            attempt + 1, result.getErrorMessage());
                    continue;
                }

                List<SpecCheckResult> specResults = result.getSpecResults();
                if (specResults == null || specResults.isEmpty()) {
                    log.warn("ConditionAdjust attempt {}: empty spec results", attempt + 1);
                    continue;
                }

                SpecCheckResult negatedResult = specResults.get(0);
                if (negatedResult.isPassed()) {
                    log.info("ConditionAdjust: ¬ρ is universally true, no condition fix possible");
                    return null;
                }

                // Extract lambda values
                String rawOutput = result.getOutput();
                Map<String, String> extractedValues = ParameterExtractor.extract(rawOutput, prep.lambdaNames);
                if (extractedValues.isEmpty()) {
                    log.warn("ConditionAdjust attempt {}: failed to extract lambda values", attempt + 1);
                    continue;
                }
                if (extractedValues.size() < prep.lambdaNames.size()) {
                    int outputHash = rawOutput != null ? rawOutput.hashCode() : 0;
                    if (!partialOutputHashes.add(outputHash)) {
                        consecutivePartials++;
                    } else {
                        consecutivePartials = 0;
                    }
                    log.warn("ConditionAdjust attempt {}: partial extraction ({}/{}), retrying without exclusion{}",
                            attempt + 1, extractedValues.size(), prep.lambdaNames.size(),
                            consecutivePartials > 0 ? " (duplicate #" + consecutivePartials + ")" : "");
                    if (consecutivePartials >= 2) {
                        log.info("ConditionAdjust: repeated partial extraction, giving up");
                        break;
                    }
                    // Do NOT add exclusion from partial values — incomplete assignment
                    // would over-exclude valid solutions from the search space.
                    continue;
                }
                consecutivePartials = 0;

                // Interpret results: determine removals and additions
                InterpretedResult ir = interpretResults(prep, extractedValues, allRules, deviceSmvMap);

                boolean anyChange = ir.adjustments.stream()
                        .anyMatch(a -> "remove".equals(a.getAction()) || "add".equals(a.getAction()));
                if (!anyChange) {
                    log.info("ConditionAdjust attempt {}: no changes, adding exclusion", attempt + 1);
                    addExclusion(exclusionInvars, extractedValues);
                    continue;
                }

                // Apply changes to a fresh copy of allRules
                List<RuleDto> modifiedRules = applyChanges(allRules, ir.conditionsToRemove, ir.conditionsToAdd);

                // Reject solutions that strip a rule down to zero trigger conditions. NuSMV treats an
                // empty-condition rule as fail-closed (never fires), so such a solution can verify — but
                // RuleDto forbids empty conditions and the apply layer rejects it, so returning it would
                // hand the user a "verified" suggestion that can never be applied. Exclude and keep searching.
                if (emptiesAnyRule(modifiedRules, ir.conditionsToRemove.keySet())) {
                    log.info("ConditionAdjust attempt {}: solution empties a rule's conditions; excluding", attempt + 1);
                    addExclusion(exclusionInvars, extractedValues);
                    continue;
                }

                // Forward verify
                if (FixStrategyUtils.forwardVerify(smvGenerator, nusmvExecutor, ctx, modifiedRules)) {
                    // Filter out action="keep" entries — they add no value for the user
                    List<ConditionAdjustment> actionableAdjustments = ir.adjustments.stream()
                            .filter(a -> !"keep".equals(a.getAction()))
                            .collect(Collectors.toList());
                    String description = buildDescription(ir.adjustments);
                    return FixSuggestionDto.builder()
                            .strategy(NAME)
                            .description("Adjust conditions: " + description)
                            .conditionAdjustments(actionableAdjustments)
                            .verified(true)
                            .build();
                }

                addExclusion(exclusionInvars, extractedValues);
                log.info("ConditionAdjust attempt {}: forward verification failed, excluding configuration", attempt + 1);

            } catch (Exception e) {
                log.warn("ConditionAdjust attempt {}: failed: {}", attempt + 1, e.getMessage(), e);
            } finally {
                FixStrategyUtils.cleanupTempDir(smvFile);
            }
        }

        log.info("ConditionAdjustStrategy: exhausted attempts without finding a fix");
        return null;
    }

    // -------- Preparation: deep copy + inject candidates + build lambdas --------

    private PreparedData prepareAugmentedRules(
            List<RuleDto> allRules,
            Set<Integer> expandedIndices,
            SpecificationDto violatedSpec,
            Map<String, DeviceSmvData> deviceSmvMap) {

        List<RuleDto> augmentedRules = FixStrategyUtils.deepCopyRules(allRules);
        Map<Integer, Integer> originalCondCounts = new HashMap<>();

        for (int ruleIdx : expandedIndices) {
            RuleDto augRule = augmentedRules.get(ruleIdx);
            originalCondCounts.put(ruleIdx, augRule.getConditions() != null
                    ? augRule.getConditions().size() : 0);

            List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                    violatedSpec, allRules.get(ruleIdx), deviceSmvMap, fixConfig.getMaxCandidatesPerRule());
            if (!candidates.isEmpty()) {
                if (augRule.getConditions() == null) {
                    augRule.setConditions(new ArrayList<>());
                }
                augRule.getConditions().addAll(candidates);
            }
        }

        // Build conditionLambdas covering all conditions (original + candidate) in expanded rules
        Map<String, String> conditionLambdas = new LinkedHashMap<>();
        List<String> lambdaNames = new ArrayList<>();

        for (int ruleIdx : expandedIndices) {
            RuleDto augRule = augmentedRules.get(ruleIdx);
            if (augRule.getConditions() == null || augRule.getConditions().isEmpty()) continue;
            for (int condIdx = 0; condIdx < augRule.getConditions().size(); condIdx++) {
                if (augRule.getConditions().get(condIdx) == null) continue;
                String key = "r" + ruleIdx + "_c" + condIdx;
                String lambdaName = "lambda_" + key;
                conditionLambdas.put(key, lambdaName);
                lambdaNames.add(lambdaName);
            }
        }

        if (conditionLambdas.isEmpty()) {
            log.info("ConditionAdjustStrategy: no conditions found in expanded rules");
            return null;
        }

        return new PreparedData(augmentedRules, originalCondCounts, conditionLambdas, lambdaNames);
    }

    // -------- Result interpretation --------

    private InterpretedResult interpretResults(
            PreparedData prep,
            Map<String, String> extractedValues,
            List<RuleDto> allRules,
            Map<String, DeviceSmvData> deviceSmvMap) {

        List<ConditionAdjustment> adjustments = new ArrayList<>();
        Map<Integer, List<Integer>> conditionsToRemove = new LinkedHashMap<>();
        Map<Integer, List<RuleDto.Condition>> conditionsToAdd = new LinkedHashMap<>();

        for (Map.Entry<String, String> entry : prep.conditionLambdas.entrySet()) {
            String key = entry.getKey();
            String lambdaName = entry.getValue();
            String lambdaValue = extractedValues.get(lambdaName);

            Matcher m = KEY_PATTERN.matcher(key);
            if (!m.matches()) {
                log.warn("ConditionAdjust: unexpected key format '{}'", key);
                continue;
            }
            int ruleIdx = Integer.parseInt(m.group(1));
            int condIdx = Integer.parseInt(m.group(2));

            int originalCount = prep.originalCondCounts.getOrDefault(ruleIdx, 0);
            RuleDto.Condition cond = prep.augmentedRules.get(ruleIdx).getConditions().get(condIdx);
            String ruleDescription = describeRule(allRules, ruleIdx);
            String deviceLabel = displayDeviceLabel(cond == null ? null : cond.getDeviceName(), deviceSmvMap);

            // [C4] fail-safe: missing lambda → keep for existing, ignore for candidate
            if (lambdaValue == null) {
                log.warn("lambda '{}' not found in NuSMV output, defaulting to {}", lambdaName,
                        condIdx < originalCount ? "keep" : "ignore");
            }

            if (condIdx < originalCount) {
                // Existing condition
                String action = "FALSE".equalsIgnoreCase(lambdaValue) ? "remove" : "keep";
                if ("remove".equals(action)) {
                    conditionsToRemove.computeIfAbsent(ruleIdx, k -> new ArrayList<>()).add(condIdx);
                }
                adjustments.add(ConditionAdjustment.builder()
                        .ruleIndex(ruleIdx).conditionIndex(condIdx)
                        .action(action)
                        .attribute(cond != null ? cond.getAttribute() : "unknown")
                        .targetType(cond != null ? cond.getTargetType() : null)
                        .ruleDescription(ruleDescription)
                        .deviceLabel(deviceLabel)
                        .deviceName(cond != null ? cond.getDeviceName() : null)
                        .relation(cond != null ? cond.getRelation() : null)
                        .value(cond != null ? cond.getValue() : null)
                        .description(action + " " + conditionSummary(deviceLabel, cond)
                                + " from " + ruleDescription)
                        .build());
            } else {
                // Candidate condition
                if ("TRUE".equalsIgnoreCase(lambdaValue)) {
                    conditionsToAdd.computeIfAbsent(ruleIdx, k -> new ArrayList<>()).add(cond);
                    adjustments.add(ConditionAdjustment.builder()
                            .ruleIndex(ruleIdx).conditionIndex(condIdx)
                            .action("add")
                            .attribute(cond.getAttribute())
                            .targetType(cond.getTargetType())
                            .ruleDescription(ruleDescription)
                            .deviceLabel(deviceLabel)
                            .deviceName(cond.getDeviceName())
                            .relation(cond.getRelation())
                            .value(cond.getValue())
                            .description("add " + conditionSummary(deviceLabel, cond)
                                    + " to " + ruleDescription)
                            .build());
                }
                // lambda=FALSE for candidate → ignore, not recorded
            }
        }

        return new InterpretedResult(adjustments, conditionsToRemove, conditionsToAdd);
    }

    // -------- Apply changes --------

    private static List<RuleDto> applyChanges(
            List<RuleDto> allRules,
            Map<Integer, List<Integer>> conditionsToRemove,
            Map<Integer, List<RuleDto.Condition>> conditionsToAdd) {

        List<RuleDto> modifiedRules = FixStrategyUtils.deepCopyRules(allRules);

        // 1) Remove (in reverse index order to preserve indices)
        for (Map.Entry<Integer, List<Integer>> e : conditionsToRemove.entrySet()) {
            List<Integer> indices = new ArrayList<>(e.getValue());
            indices.sort(Collections.reverseOrder());
            List<RuleDto.Condition> conds = modifiedRules.get(e.getKey()).getConditions();
            for (int idx : indices) {
                if (idx < conds.size()) conds.remove(idx);
            }
        }
        // 2) Add
        for (Map.Entry<Integer, List<RuleDto.Condition>> e : conditionsToAdd.entrySet()) {
            List<RuleDto.Condition> conds = modifiedRules.get(e.getKey()).getConditions();
            if (conds == null) {
                conds = new ArrayList<>();
                modifiedRules.get(e.getKey()).setConditions(conds);
            }
            conds.addAll(e.getValue());
        }

        return modifiedRules;
    }

    /**
     * True if applying the changes leaves any affected rule with zero trigger conditions. Only rules
     * that had conditions removed can be emptied (adds never reduce the count), so we check those.
     */
    private static boolean emptiesAnyRule(List<RuleDto> modifiedRules, Set<Integer> touchedRuleIndices) {
        for (int ruleIdx : touchedRuleIndices) {
            if (ruleIdx < 0 || ruleIdx >= modifiedRules.size()) continue;
            List<RuleDto.Condition> conds = modifiedRules.get(ruleIdx).getConditions();
            if (conds == null || conds.isEmpty()) {
                return true;
            }
        }
        return false;
    }

    // -------- Description builder --------

    private static String buildDescription(List<ConditionAdjustment> adjustments) {
        return adjustments.stream()
                .filter(a -> "remove".equals(a.getAction()) || "add".equals(a.getAction()))
                .map(ConditionAdjustStrategy::sentenceCase)
                .collect(Collectors.joining("; "));
    }

    private static String sentenceCase(ConditionAdjustment adjustment) {
        String description = adjustment.getDescription();
        if (description == null || description.isBlank()) {
            return adjustment.getAction();
        }
        return Character.toUpperCase(description.charAt(0)) + description.substring(1);
    }

    private static String describeRule(List<RuleDto> rules, int ruleIndex) {
        if (rules != null && ruleIndex >= 0 && ruleIndex < rules.size()) {
            RuleDto rule = rules.get(ruleIndex);
            if (rule != null && rule.getRuleString() != null && !rule.getRuleString().isBlank()) {
                return "'" + rule.getRuleString() + "'";
            }
        }
        return "affected rule";
    }

    private static String displayDeviceLabel(String deviceRef, Map<String, DeviceSmvData> deviceSmvMap) {
        if (deviceRef != null && deviceSmvMap != null) {
            try {
                DeviceSmvData smv = DeviceReferenceResolver.resolve(deviceRef, deviceSmvMap);
                if (smv != null && smv.getDeviceLabel() != null && !smv.getDeviceLabel().isBlank()) {
                    return smv.getDeviceLabel();
                }
            } catch (RuntimeException ignored) {
                // The adjustment remains structurally useful; do not expose the unresolved model id.
            }
        }
        return "unknown device";
    }

    private static String conditionSummary(String deviceLabel, RuleDto.Condition condition) {
        if (condition == null) return deviceLabel + ".unknown condition";
        StringBuilder summary = new StringBuilder(deviceLabel)
                .append('.').append(condition.getAttribute() == null ? "unknown" : condition.getAttribute());
        if (condition.getRelation() != null && !condition.getRelation().isBlank()) {
            summary.append(' ').append(condition.getRelation());
        }
        if (condition.getValue() != null && !condition.getValue().isBlank()) {
            summary.append(' ').append(condition.getValue());
        }
        return summary.toString();
    }

    // -------- Helpers --------

    private static void addExclusion(List<String> exclusionInvars, Map<String, String> extractedValues) {
        StringBuilder exclusion = new StringBuilder("!(");
        List<String> eqParts = new ArrayList<>();
        for (Map.Entry<String, String> ev : extractedValues.entrySet()) {
            eqParts.add(ev.getKey() + "=" + ev.getValue());
        }
        exclusion.append(String.join(" & ", eqParts)).append(")");
        exclusionInvars.add(exclusion.toString());
    }

    // -------- Internal records --------

    private record PreparedData(
            List<RuleDto> augmentedRules,
            Map<Integer, Integer> originalCondCounts,
            Map<String, String> conditionLambdas,
            List<String> lambdaNames
    ) {}

    private record InterpretedResult(
            List<ConditionAdjustment> adjustments,
            Map<Integer, List<Integer>> conditionsToRemove,
            Map<Integer, List<RuleDto.Condition>> conditionsToAdd
    ) {}
}
