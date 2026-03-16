package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixContext;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixStrategy;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize.ParameterizationConfig;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize.ParameterExtractor;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.NusmvResult;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor.SpecCheckResult;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvRelationUtils;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.fix.ParameterAdjustment;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.io.File;
import java.util.*;
import java.util.stream.Collectors;

/**
 * §5.1 Rule Parameter Adjustment (Salus paper).
 *
 * <p>Parameterizes numeric thresholds in fault rules as FROZENVAR,
 * uses NuSMV with negated spec (¬ρ) to find corrective values,
 * then verifies the candidate fix.</p>
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class ParameterAdjustStrategy implements FixStrategy {

    private static final String NAME = "parameter";
    private static final Set<String> NUMERIC_RELATIONS = Set.of(">", ">=", "<", "<=");

    private final SmvGenerator smvGenerator;
    private final NusmvExecutor nusmvExecutor;
    private final FixConfig fixConfig;

    // §5.3 refinement: three-state result from NuSMV-guided candidate search (heuristic extension of paper §5.1)
    private enum RefineStatus { CANDIDATE, UNSAT, ERROR }

    private record RefineResult(RefineStatus status, Integer candidateValue) {
        static RefineResult candidate(int value) { return new RefineResult(RefineStatus.CANDIDATE, value); }
        static RefineResult unsat() { return new RefineResult(RefineStatus.UNSAT, null); }
        static RefineResult error() { return new RefineResult(RefineStatus.ERROR, null); }
    }

    @Override
    public String name() {
        return NAME;
    }

    @Override
    public FixSuggestionDto tryFix(FixContext ctx) {
        List<FaultRuleDto> faultRules = ctx.getFaultRules();
        List<RuleDto> allRules = ctx.getAllRules();
        Map<String, DeviceSmvData> deviceSmvMap = ctx.getDeviceSmvMap();
        int violatedSpecIndex = ctx.getViolatedSpecIndex();
        int maxAttempts = ctx.getMaxAttempts() > 0 ? ctx.getMaxAttempts() : 20;

        if (faultRules == null || faultRules.isEmpty()) return null;

        // §5: Expand parameterization scope to rules sharing devices with violated spec
        SpecificationDto violatedSpec = ctx.getSpecs().get(violatedSpecIndex);
        Set<Integer> expandedIndices = FixStrategyUtils.expandRuleIndices(
                faultRules, allRules, violatedSpec, deviceSmvMap);

        // Step 1: Identify parameterizable numeric conditions in expanded rule set
        Map<String, ParameterizationConfig.ParamInfo> thresholds = new LinkedHashMap<>();
        List<ParameterAdjustment> adjustmentTemplate = new ArrayList<>();

        for (int ruleIdx : expandedIndices) {
            RuleDto rule = allRules.get(ruleIdx);
            if (rule.getConditions() == null) continue;

            for (int condIdx = 0; condIdx < rule.getConditions().size(); condIdx++) {
                RuleDto.Condition cond = rule.getConditions().get(condIdx);
                if (cond == null || cond.getRelation() == null || cond.getValue() == null) continue;

                String normalizedRel = SmvRelationUtils.normalizeRelation(cond.getRelation());
                if (!NUMERIC_RELATIONS.contains(normalizedRel)) continue;

                // Check if value is numeric
                try {
                    Double.parseDouble(cond.getValue().trim());
                } catch (NumberFormatException e) {
                    continue;
                }

                // Resolve bounds from device template
                int[] bounds = resolveBounds(cond, deviceSmvMap);
                if (bounds == null) continue;

                String key = "r" + ruleIdx + "_c" + condIdx;
                String frozenVarName = "param_" + key;

                // Apply preferred range intersection if specified
                PreferredRange preferred = (ctx.getPreferredRanges() != null)
                        ? ctx.getPreferredRanges().get(key) : null;
                if (preferred != null) {
                    int prefLower = Math.max(bounds[0], preferred.getLower());
                    int prefUpper = Math.min(bounds[1], preferred.getUpper());
                    if (prefLower > prefUpper) {
                        log.warn("Preferred range [{},{}] has no intersection with template bounds [{},{}] for {}, skipping",
                                preferred.getLower(), preferred.getUpper(), bounds[0], bounds[1], key);
                        continue;
                    }
                    bounds = new int[]{prefLower, prefUpper};
                }

                thresholds.put(key, ParameterizationConfig.ParamInfo.builder()
                        .frozenVarName(frozenVarName)
                        .lowerBound(bounds[0])
                        .upperBound(bounds[1])
                        .originalValue(cond.getValue().trim())
                        .build());

                adjustmentTemplate.add(ParameterAdjustment.builder()
                        .ruleIndex(ruleIdx)
                        .conditionIndex(condIdx)
                        .attribute(cond.getAttribute())
                        .relation(normalizedRel)
                        .originalValue(cond.getValue().trim())
                        .lowerBound(bounds[0])
                        .upperBound(bounds[1])
                        .build());
            }
        }

        if (thresholds.isEmpty()) {
            log.info("ParameterAdjustStrategy: no numeric conditions found in fault rules");
            return null;
        }

        log.info("ParameterAdjustStrategy: found {} parameterizable threshold(s)", thresholds.size());

        // Step 2: Iterate with NuSMV
        List<String> exclusionInvars = new ArrayList<>();
        List<String> frozenVarNames = thresholds.values().stream()
                .map(ParameterizationConfig.ParamInfo::getFrozenVarName)
                .collect(Collectors.toList());

        for (int attempt = 0; attempt < maxAttempts; attempt++) {
            if (ctx.isExpired()) {
                log.info("ParameterAdjustStrategy: deadline expired at attempt {}/{}", attempt + 1, maxAttempts);
                break;
            }
            ParameterizationConfig config = ParameterizationConfig.builder()
                    .parameterizedThresholds(thresholds)
                    .negatedSpecIndex(violatedSpecIndex)
                    .exclusionInvars(new ArrayList<>(exclusionInvars))
                    .build();

            // Step 2a: Generate parameterized model with ¬ρ
            File smvFile = null;
            try {
                SmvGenerator.GenerateResult genResult = smvGenerator.generateParameterized(
                        ctx.getUserId(), ctx.getDevices(), allRules, ctx.getSpecs(),
                        ctx.isAttack(), ctx.getIntensity(), ctx.isEnablePrivacy(), config);
                if (genResult == null) {
                    log.warn("ParameterAdjust attempt {}: SMV generation returned null", attempt + 1);
                    continue;
                }
                smvFile = genResult.smvFile();

                NusmvResult result = nusmvExecutor.execute(smvFile);
                if (!result.isSuccess()) {
                    log.warn("ParameterAdjust attempt {}: NuSMV execution failed: {}",
                            attempt + 1, result.getErrorMessage());
                    continue;
                }

                // Step 2b: Check ¬ρ result
                List<SpecCheckResult> specResults = result.getSpecResults();
                if (specResults == null || specResults.isEmpty()) {
                    log.warn("ParameterAdjust attempt {}: empty spec results", attempt + 1);
                    continue;
                }

                SpecCheckResult negatedResult = specResults.get(0);
                if (negatedResult.isPassed()) {
                    // ¬ρ universally true — more INVARs only restrict further, cannot help
                    log.info("ParameterAdjust: ¬ρ is universally true, no parameter fix possible");
                    return null;
                }

                // Step 2c: Extract FROZENVAR values from counterexample
                String rawOutput = result.getOutput();
                Map<String, String> extractedValues = ParameterExtractor.extract(rawOutput, frozenVarNames);
                if (extractedValues.isEmpty()) {
                    log.warn("ParameterAdjust attempt {}: failed to extract FROZENVAR values", attempt + 1);
                    continue;
                }

                // Step 2d: Build candidate adjustments
                List<ParameterAdjustment> candidateAdjustments = new ArrayList<>();
                List<RuleDto> modifiedRules = FixStrategyUtils.deepCopyRules(allRules);
                boolean allExtracted = true;

                for (ParameterAdjustment template : adjustmentTemplate) {
                    String key = "r" + template.getRuleIndex() + "_c" + template.getConditionIndex();
                    ParameterizationConfig.ParamInfo paramInfo = thresholds.get(key);
                    String newValue = extractedValues.get(paramInfo.getFrozenVarName());
                    if (newValue == null) {
                        allExtracted = false;
                        break;
                    }

                    candidateAdjustments.add(ParameterAdjustment.builder()
                            .ruleIndex(template.getRuleIndex())
                            .conditionIndex(template.getConditionIndex())
                            .attribute(template.getAttribute())
                            .relation(template.getRelation())
                            .originalValue(template.getOriginalValue())
                            .newValue(newValue)
                            .lowerBound(template.getLowerBound())
                            .upperBound(template.getUpperBound())
                            .build());

                    // Apply to modified rules
                    RuleDto rule = modifiedRules.get(template.getRuleIndex());
                    rule.getConditions().get(template.getConditionIndex()).setValue(newValue);
                }

                if (!allExtracted) {
                    log.warn("ParameterAdjust attempt {}: incomplete FROZENVAR extraction", attempt + 1);
                    continue;
                }

                // Step 2e: Forward-verify with modified rules
                if (FixStrategyUtils.forwardVerify(smvGenerator, nusmvExecutor, ctx, modifiedRules)) {
                    // §5.3: Refine to closest original values
                    refineToClosest(candidateAdjustments, thresholds, extractedValues, allRules, ctx);

                    String description = candidateAdjustments.stream()
                            .map(a -> {
                                String base = "Rule " + a.getRuleIndex() + " cond " + a.getConditionIndex()
                                        + ": " + a.getAttribute() + a.getRelation()
                                        + a.getOriginalValue() + " → " + a.getAttribute()
                                        + a.getRelation() + a.getNewValue();
                                // Add clarification when threshold hits the variable boundary
                                Integer newVal = safeParseInt(a.getNewValue());
                                if (newVal != null && (newVal == a.getUpperBound() || newVal == a.getLowerBound())) {
                                    base += " (boundary value — rule effectively disabled)";
                                }
                                return base;
                            })
                            .collect(Collectors.joining("; "));

                    return FixSuggestionDto.builder()
                            .strategy(NAME)
                            .description("Adjust parameter(s): " + description)
                            .parameterAdjustments(candidateAdjustments)
                            .verified(true)
                            .build();
                }

                // Step 2f: Add INVAR to exclude this configuration and retry
                StringBuilder exclusion = new StringBuilder("!(");
                List<String> eqParts = new ArrayList<>();
                for (Map.Entry<String, String> entry : extractedValues.entrySet()) {
                    eqParts.add(entry.getKey() + "=" + entry.getValue());
                }
                exclusion.append(String.join(" & ", eqParts)).append(")");
                exclusionInvars.add(exclusion.toString());

                log.info("ParameterAdjust attempt {}: forward verification failed, excluding configuration", attempt + 1);

            } catch (Exception e) {
                log.warn("ParameterAdjust attempt {}: failed: {}", attempt + 1, e.getMessage(), e);
                // Continue to next attempt — exception may be transient or INVAR-dependent
            } finally {
                FixStrategyUtils.cleanupTempDir(smvFile);
            }
        }

        log.info("ParameterAdjustStrategy: exhausted attempts without finding a fix");
        return null;
    }

    // ======================== §5.3: Refine to closest original ========================

    /**
     * §5.3 NuSMV-guided branch-and-bound refinement (heuristic extension of paper §5.1/§5.3).
     *
     * <p>For each parameter, uses distance-based range narrowing with NuSMV ¬ρ to find
     * a valid value closer to the original than the initial discovery. Does not assume
     * monotonicity — uses exclusion constraints instead of binary search pruning.</p>
     *
     * <p>Budget: maxRefineAttempts counts refinement loop iterations (each = 1 NuSMV ¬ρ + up to 1
     * forward-verify). The try-original step is outside the budget (extra cost ≤ param count).
     * Total NuSMV calls ≤ paramCount + maxRefineAttempts × 2.
     * Budget is shared across all parameters: if the original value is not pre-excluded and
     * NuSMV re-returns it in the loop, up to two iterations may be consumed per parameter
     * (first verify fails → un-exclude → retry). With many parameters and a small
     * maxRefineAttempts, later parameters may have reduced refinement capacity.</p>
     */
    private void refineToClosest(
            List<ParameterAdjustment> candidateAdjustments,
            Map<String, ParameterizationConfig.ParamInfo> thresholds,
            Map<String, String> discoveredValues,
            List<RuleDto> allRules,
            FixContext ctx) {

        int[] remainingBudget = { fixConfig.getMaxRefineAttempts() };

        for (ParameterAdjustment adj : candidateAdjustments) {
            if (remainingBudget[0] <= 0 || ctx.isExpired()) break;

            int original;
            int current;
            try {
                original = Integer.parseInt(adj.getOriginalValue());
                current = Integer.parseInt(adj.getNewValue());
            } catch (NumberFormatException e) {
                continue;
            }

            String paramKey = "r" + adj.getRuleIndex() + "_c" + adj.getConditionIndex();
            ParameterizationConfig.ParamInfo paramInfo = thresholds.get(paramKey);
            if (paramInfo == null) continue;

            int best = current;
            int bestDist = Math.abs(best - original);

            // Step A: Try original value (other params changed, original may now work; not counted in budget)
            if (bestDist > 0) {
                List<RuleDto> testRules = FixStrategyUtils.deepCopyRules(allRules);
                for (Map.Entry<String, ParameterizationConfig.ParamInfo> e : thresholds.entrySet()) {
                    String value;
                    if (e.getKey().equals(paramKey)) {
                        value = String.valueOf(original);
                    } else {
                        value = discoveredValues.get(e.getValue().getFrozenVarName());
                        if (value == null) continue;
                    }
                    applyParamValue(testRules, e.getKey(), value);
                }
                try {
                    if (FixStrategyUtils.forwardVerify(smvGenerator, nusmvExecutor, ctx, testRules)) {
                        best = original;
                        bestDist = 0;
                    }
                } catch (Exception e) {
                    log.warn("refineToClosest: original-value test failed: {}", e.getMessage());
                }
            }

            if (bestDist <= 1) {
                adj.setNewValue(String.valueOf(best));
                discoveredValues.put(paramInfo.getFrozenVarName(), String.valueOf(best));
                continue;
            }

            // Step B: NuSMV-guided branch-and-bound loop
            Set<Integer> exclusionValues = new HashSet<>();
            exclusionValues.add(current); // don't re-return the initial discovered value
            Set<Integer> seen = new HashSet<>();
            seen.add(current);
            // original NOT excluded here: forwardVerify conflates genuine infeasibility
            // with tool errors (both return false). If NuSMV re-discovers original in the
            // loop, it costs at most 2 budget iterations (first verify fails → un-exclude
            // → retry) and allows recovery from transient failures (achieving distance=0).

            int consecutiveErrors = 0;
            boolean originalRetried = false;

            // Prepare baseRules with other params fixed at discovered values
            List<RuleDto> baseRules = FixStrategyUtils.deepCopyRules(allRules);
            for (Map.Entry<String, ParameterizationConfig.ParamInfo> e : thresholds.entrySet()) {
                if (e.getKey().equals(paramKey)) continue;
                String value = discoveredValues.get(e.getValue().getFrozenVarName());
                if (value != null) {
                    applyParamValue(baseRules, e.getKey(), value);
                }
            }

            refineLoop:
            while (remainingBudget[0] > 0 && bestDist > 1) {
                if (ctx.isExpired()) break;

                int L = Math.max(paramInfo.getLowerBound(), original - bestDist + 1);
                int U = Math.min(paramInfo.getUpperBound(), original + bestDist - 1);
                if (L > U) break;

                remainingBudget[0]--;

                // Build exclusion INVARs
                List<String> exclusionInvars = new ArrayList<>();
                for (int excl : exclusionValues) {
                    exclusionInvars.add("!(" + paramInfo.getFrozenVarName() + "=" + excl + ")");
                }

                RefineResult result = nusmvSolveForRefine(paramKey, L, U, thresholds,
                        exclusionInvars, baseRules, ctx);

                switch (result.status()) {
                    case UNSAT:
                        break refineLoop;
                    case ERROR:
                        consecutiveErrors++;
                        if (consecutiveErrors >= 3) break refineLoop;
                        continue refineLoop;
                    case CANDIDATE:
                        consecutiveErrors = 0;
                        int cand = result.candidateValue();
                        exclusionValues.add(cand);
                        if (seen.contains(cand)) continue refineLoop;
                        seen.add(cand);

                        // Forward-verify the candidate (from baseRules copy, never mutate baseRules)
                        try {
                            List<RuleDto> verifyRules = FixStrategyUtils.deepCopyRules(baseRules);
                            applyParamValue(verifyRules, paramKey, String.valueOf(cand));
                            if (FixStrategyUtils.forwardVerify(smvGenerator, nusmvExecutor, ctx, verifyRules)) {
                                best = cand;
                                bestDist = Math.abs(cand - original);
                            } else if (cand == original && !originalRetried) {
                                // forwardVerify can't distinguish genuine infeasibility from
                                // tool error. Un-exclude original to allow one more NuSMV retry.
                                // Cost: ≤1 extra iteration if original is genuinely infeasible.
                                exclusionValues.remove(cand);
                                seen.remove(cand);
                                originalRetried = true;
                            }
                        } catch (Exception e) {
                            if (cand == original && !originalRetried) {
                                exclusionValues.remove(cand);
                                seen.remove(cand);
                                originalRetried = true;
                            }
                            log.warn("refineToClosest: candidate {} verify failed: {}", cand, e.getMessage());
                        }
                        continue refineLoop;
                }
            }

            adj.setNewValue(String.valueOf(best));
            discoveredValues.put(paramInfo.getFrozenVarName(), String.valueOf(best));
        }
    }

    /**
     * Run a single-param parameterized NuSMV solve for refinement.
     *
     * <p>Builds a ParameterizationConfig with only the target param as FROZENVAR (narrowed bounds),
     * other params already applied to rulesWithOtherParamsApplied. Returns three-state result.</p>
     *
     * <p>UNSAT: only when NuSMV successfully executes AND ¬ρ passes (no satisfying assignment).
     * All other failures (execution error, extraction failure, out-of-bounds) → ERROR.</p>
     */
    private RefineResult nusmvSolveForRefine(
            String paramKey, int narrowedLower, int narrowedUpper,
            Map<String, ParameterizationConfig.ParamInfo> allThresholds,
            List<String> exclusionInvars,
            List<RuleDto> rulesWithOtherParamsApplied,
            FixContext ctx) {

        ParameterizationConfig.ParamInfo originalInfo = allThresholds.get(paramKey);
        ParameterizationConfig.ParamInfo narrowed = ParameterizationConfig.ParamInfo.builder()
                .frozenVarName(originalInfo.getFrozenVarName())
                .lowerBound(narrowedLower)
                .upperBound(narrowedUpper)
                .originalValue(originalInfo.getOriginalValue())
                .build();

        Map<String, ParameterizationConfig.ParamInfo> singleParam = new LinkedHashMap<>();
        singleParam.put(paramKey, narrowed);

        ParameterizationConfig config = ParameterizationConfig.builder()
                .parameterizedThresholds(singleParam)
                .negatedSpecIndex(ctx.getViolatedSpecIndex())
                .exclusionInvars(new ArrayList<>(exclusionInvars))
                .build();

        File smvFile = null;
        try {
            SmvGenerator.GenerateResult genResult = smvGenerator.generateParameterized(
                    ctx.getUserId(), ctx.getDevices(), rulesWithOtherParamsApplied, ctx.getSpecs(),
                    ctx.isAttack(), ctx.getIntensity(), ctx.isEnablePrivacy(), config);
            if (genResult == null) return RefineResult.error();
            smvFile = genResult.smvFile();

            NusmvResult result = nusmvExecutor.execute(smvFile);
            if (!result.isSuccess()) {
                log.warn("nusmvSolveForRefine: execution failed: {}", result.getErrorMessage());
                return RefineResult.error();
            }

            List<SpecCheckResult> specResults = result.getSpecResults();
            if (specResults == null || specResults.isEmpty()) return RefineResult.error();

            if (specResults.get(0).isPassed()) {
                // ¬ρ universally true → no satisfying assignment in [L,U] minus exclusions
                return RefineResult.unsat();
            }

            // Extract FROZENVAR value from counterexample
            Map<String, String> extracted = ParameterExtractor.extract(
                    result.getOutput(), List.of(narrowed.getFrozenVarName()));
            String valueStr = extracted.get(narrowed.getFrozenVarName());
            if (valueStr == null) {
                log.warn("nusmvSolveForRefine: failed to extract value for {}", narrowed.getFrozenVarName());
                return RefineResult.error();
            }

            int cand;
            try {
                cand = Integer.parseInt(valueStr);
            } catch (NumberFormatException e) {
                log.warn("nusmvSolveForRefine: non-integer value '{}' for {}", valueStr, narrowed.getFrozenVarName());
                return RefineResult.error();
            }

            // Bounds check (defensive — NuSMV should respect FROZENVAR range, but guard against edge cases)
            if (cand < narrowedLower || cand > narrowedUpper) {
                log.warn("nusmvSolveForRefine: candidate {} outside [{},{}], treating as error",
                        cand, narrowedLower, narrowedUpper);
                return RefineResult.error();
            }

            return RefineResult.candidate(cand);

        } catch (Exception e) {
            log.warn("nusmvSolveForRefine: exception: {}", e.getMessage(), e);
            return RefineResult.error();
        } finally {
            FixStrategyUtils.cleanupTempDir(smvFile);
        }
    }

    /** Apply a param value to rules by parsing the key "r{ruleIdx}_c{condIdx}". */
    private static void applyParamValue(List<RuleDto> rules, String key, String value) {
        String[] parts = key.replace("r", "").split("_c");
        if (parts.length != 2) return;
        try {
            int ruleIdx = Integer.parseInt(parts[0]);
            int condIdx = Integer.parseInt(parts[1]);
            if (ruleIdx < rules.size()) {
                RuleDto rule = rules.get(ruleIdx);
                if (rule.getConditions() != null && condIdx < rule.getConditions().size()) {
                    rule.getConditions().get(condIdx).setValue(value);
                }
            }
        } catch (NumberFormatException ignored) {
            // skip
        }
    }

    // ======================== Helpers ========================

    private int[] resolveBounds(RuleDto.Condition condition, Map<String, DeviceSmvData> deviceSmvMap) {
        String deviceId = condition.getDeviceName();
        if (deviceId == null) return null;

        DeviceSmvData smv;
        try {
            smv = DeviceSmvDataFactory.findDeviceSmvDataStrict(deviceId, deviceSmvMap);
        } catch (Exception e) {
            return null;
        }
        if (smv == null) return null;

        String attr = condition.getAttribute();
        if (attr == null) return null;

        // Check internal variables
        if (smv.getVariables() != null) {
            for (DeviceManifest.InternalVariable var : smv.getVariables()) {
                if (var != null && attr.equals(var.getName())
                        && var.getLowerBound() != null && var.getUpperBound() != null) {
                    return new int[]{var.getLowerBound(), var.getUpperBound()};
                }
            }
        }

        // Check env variables
        if (smv.getEnvVariables() != null) {
            String envKey = attr.startsWith("a_") ? attr.substring(2) : attr;
            DeviceManifest.InternalVariable envVar = smv.getEnvVariables().get(envKey);
            if (envVar != null && envVar.getLowerBound() != null && envVar.getUpperBound() != null) {
                return new int[]{envVar.getLowerBound(), envVar.getUpperBound()};
            }
        }

        return null;
    }

    /** Parse int safely, returning null on failure (non-integer NuSMV output). */
    private static Integer safeParseInt(String s) {
        if (s == null) return null;
        try {
            return Integer.parseInt(s.trim());
        } catch (NumberFormatException e) {
            return null;
        }
    }
}
