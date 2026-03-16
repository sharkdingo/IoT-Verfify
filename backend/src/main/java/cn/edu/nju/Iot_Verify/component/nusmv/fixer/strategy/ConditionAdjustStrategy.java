package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixContext;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixStrategy;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize.ParameterizationConfig;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize.ParameterExtractor;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
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
                SmvGenerator.GenerateResult genResult = smvGenerator.generateParameterized(
                        ctx.getUserId(), ctx.getDevices(), prep.augmentedRules, ctx.getSpecs(),
                        ctx.isAttack(), ctx.getIntensity(), ctx.isEnablePrivacy(), config);
                if (genResult == null) {
                    log.warn("ConditionAdjust attempt {}: SMV generation returned null", attempt + 1);
                    continue;
                }
                smvFile = genResult.smvFile();

                NusmvResult result = nusmvExecutor.execute(smvFile);
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
                InterpretedResult ir = interpretResults(prep, extractedValues, allRules);

                boolean anyChange = ir.adjustments.stream()
                        .anyMatch(a -> "remove".equals(a.getAction()) || "add".equals(a.getAction()));
                if (!anyChange) {
                    log.info("ConditionAdjust attempt {}: no changes, adding exclusion", attempt + 1);
                    addExclusion(exclusionInvars, extractedValues);
                    continue;
                }

                // Apply changes to a fresh copy of allRules
                List<RuleDto> modifiedRules = applyChanges(allRules, ir.conditionsToRemove, ir.conditionsToAdd);

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
            List<RuleDto> allRules) {

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
                        .description(action + " condition " + condIdx + " of rule " + ruleIdx
                                + " (" + (cond != null ? cond.getAttribute() : "?") + ")")
                        .build());
            } else {
                // Candidate condition
                if ("TRUE".equalsIgnoreCase(lambdaValue)) {
                    conditionsToAdd.computeIfAbsent(ruleIdx, k -> new ArrayList<>()).add(cond);
                    adjustments.add(ConditionAdjustment.builder()
                            .ruleIndex(ruleIdx).conditionIndex(condIdx)
                            .action("add")
                            .attribute(cond.getAttribute())
                            .deviceName(cond.getDeviceName())
                            .relation(cond.getRelation())
                            .value(cond.getValue())
                            .description("add condition to rule " + ruleIdx
                                    + " (" + cond.getDeviceName() + "." + cond.getAttribute() + ")")
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

    // -------- Description builder --------

    private static String buildDescription(List<ConditionAdjustment> adjustments) {
        return adjustments.stream()
                .filter(a -> "remove".equals(a.getAction()) || "add".equals(a.getAction()))
                .map(a -> {
                    if ("remove".equals(a.getAction())) {
                        return "Remove condition " + a.getConditionIndex()
                                + " of rule " + a.getRuleIndex() + " (" + a.getAttribute() + ")";
                    } else {
                        return "Add condition to rule " + a.getRuleIndex()
                                + " (" + a.getDeviceName() + "." + a.getAttribute() + ")";
                    }
                })
                .collect(Collectors.joining("; "));
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
