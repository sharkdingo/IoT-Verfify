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
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceReferenceResolver;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.fix.ParameterAdjustment;
import cn.edu.nju.Iot_Verify.dto.fix.ParameterTarget;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRangeSelection;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
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

    private record SingleParameterSearchResult(FixSuggestionDto suggestion, int attempts) {}

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
        int eligibleTargetCount = 0;
        int preferredRangeEmptyIntersections = 0;

        for (int ruleIdx : expandedIndices) {
            RuleDto rule = allRules.get(ruleIdx);
            if (rule.getConditions() == null) continue;

            for (int condIdx = 0; condIdx < rule.getConditions().size(); condIdx++) {
                RuleDto.Condition cond = rule.getConditions().get(condIdx);
                if (cond == null || cond.getRelation() == null || cond.getValue() == null) continue;

                String normalizedRel = SmvRelationUtils.normalizeRelation(cond.getRelation());
                if (!NUMERIC_RELATIONS.contains(normalizedRel)) continue;

                // Template numeric domains are integer ranges, so decimal thresholds are not valid targets.
                int originalValue;
                try {
                    originalValue = Integer.parseInt(cond.getValue().trim());
                } catch (NumberFormatException e) {
                    continue;
                }

                // Resolve bounds from device template
                int[] bounds = resolveBounds(cond, deviceSmvMap);
                if (bounds == null || bounds[0] >= bounds[1]
                        || originalValue < bounds[0] || originalValue > bounds[1]) continue;

                String key = "r" + ruleIdx + "_c" + condIdx;
                String targetId = PreferredRangeSelection.targetIdFor(ctx.getTraceId(), ruleIdx, condIdx);
                String frozenVarName = "param_" + key;
                eligibleTargetCount++;
                ctx.registerParameterTarget(ParameterTarget.builder()
                        .targetId(targetId)
                        .ruleIndex(ruleIdx)
                        .conditionIndex(condIdx)
                        .attribute(cond.getAttribute())
                        .relation(normalizedRel)
                        .originalValue(cond.getValue().trim())
                        .lowerBound(bounds[0])
                        .upperBound(bounds[1])
                        .description(describeParameterTarget(allRules, ruleIdx, condIdx, cond,
                                normalizedRel))
                        .build());

                // Apply preferred range intersection if specified
                PreferredRange preferred = (ctx.getPreferredRanges() != null)
                        ? ctx.getPreferredRanges().get(targetId) : null;
                if (preferred != null) {
                    ctx.markPreferredRangeTargetMatched(targetId);
                    int prefLower = Math.max(bounds[0], preferred.getLower());
                    int prefUpper = Math.min(bounds[1], preferred.getUpper());
                    if (prefLower > prefUpper) {
                        preferredRangeEmptyIntersections++;
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
                        .targetId(targetId)
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
            if (eligibleTargetCount == 0) {
                ctx.recordStrategyNoResult(NAME, "SKIPPED_NO_PARAMETERIZABLE_VALUES",
                        "No expanded fault rule contains a bounded numeric inequality that the parameter strategy can adjust.");
            } else if (preferredRangeEmptyIntersections == eligibleTargetCount) {
                ctx.recordStrategyNoResult(NAME, "NO_VERIFIED_SUGGESTION",
                        "Every eligible numeric target was excluded because its preferred range does not overlap the declared template bounds.");
            }
            return null;
        }

        ctx.initializeStrategySearch(NAME, maxAttempts);
        log.info("ParameterAdjustStrategy: found {} parameterizable threshold(s)", thresholds.size());

        // §5.3/user intent: before enumerating a Cartesian product, try the smaller repair
        // class in which exactly one threshold changes. Values are checked nearest-first and
        // final verification covers every initial state and every submitted specification.
        if (thresholds.size() > 1 && maxAttempts > 1) {
            int singleParameterBudget = Math.max(1, maxAttempts / 2);
            SingleParameterSearchResult singleParameterResult = tryClosestSingleParameterFix(
                    adjustmentTemplate, allRules, violatedSpec, faultRules,
                    singleParameterBudget, ctx);
            ctx.addStrategyAttempts(NAME, singleParameterResult.attempts());
            if (singleParameterResult.suggestion() != null) {
                return singleParameterResult.suggestion();
            }
            maxAttempts = Math.max(0, maxAttempts - singleParameterResult.attempts());
            if (maxAttempts == 0) {
                log.info("ParameterAdjustStrategy: minimal-change probe exhausted the full search budget");
                recordBudgetExhausted(ctx);
                return null;
            }
        }

        // Redundant automations can require several thresholds to move together: changing either
        // rule alone leaves the other one able to reproduce the violation. Before invoking the
        // Cartesian FROZENVAR solve, try one deterministic coordinated boundary candidate for
        // rules that issue the same command as a localized fault rule.
        if (thresholds.size() > 1 && maxAttempts > 0) {
            SingleParameterSearchResult coordinatedResult = tryCoordinatedPolicyFix(
                    adjustmentTemplate, allRules, violatedSpec, faultRules, ctx);
            ctx.addStrategyAttempts(NAME, coordinatedResult.attempts());
            if (coordinatedResult.suggestion() != null) {
                return coordinatedResult.suggestion();
            }
            maxAttempts = Math.max(0, maxAttempts - coordinatedResult.attempts());
            if (maxAttempts == 0) {
                recordBudgetExhausted(ctx);
                return null;
            }
        }

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
            ctx.addStrategyAttempts(NAME, 1);
            ParameterizationConfig config = ParameterizationConfig.builder()
                    .parameterizedThresholds(thresholds)
                    .negatedSpecIndex(violatedSpecIndex)
                    .exclusionInvars(new ArrayList<>(exclusionInvars))
                    .build();

            // Step 2a: Generate parameterized model with ¬ρ
            File smvFile = null;
            try {
                SmvGenerator.GenerateResult genResult =
                        FixStrategyUtils.generateParameterizedResolved(
                                smvGenerator, ctx, allRules, config);
                if (genResult == null) {
                    log.warn("ParameterAdjust attempt {}: SMV generation returned null", attempt + 1);
                    ctx.recordStrategyGenerationFailure(NAME,
                            "The parameter candidate model could not preserve the original attack scenario.");
                    return null;
                }
                if (!FixStrategyUtils.candidateModelComplete(genResult, ctx, NAME)) {
                    return null;
                }
                smvFile = genResult.smvFile();

                NusmvResult result = FixStrategyUtils.executeWithinDeadline(nusmvExecutor, smvFile, ctx);
                if (!result.isSuccess()) {
                    log.warn("ParameterAdjust attempt {}: NuSMV execution failed: {}",
                            attempt + 1, result.getErrorMessage());
                    FixStrategyUtils.recordSolverFailure(ctx, NAME,
                            "NuSMV failed while searching for parameter values.");
                    continue;
                }

                // Step 2b: Check ¬ρ result
                List<SpecCheckResult> specResults = result.getSpecResults();
                if (specResults == null || specResults.isEmpty()) {
                    log.warn("ParameterAdjust attempt {}: empty spec results", attempt + 1);
                    FixStrategyUtils.recordSolverFailure(ctx, NAME,
                            "NuSMV returned no usable specification result during parameter search.");
                    continue;
                }

                SpecCheckResult negatedResult = specResults.get(0);
                if (negatedResult.isPassed()) {
                    // ¬ρ universally true — more INVARs only restrict further, cannot help
                    log.info("ParameterAdjust: ¬ρ is universally true, no parameter fix possible");
                    ctx.clearStrategySolverFailure(NAME);
                    return null;
                }

                // Step 2c: Extract FROZENVAR values from counterexample
                String rawOutput = result.getOutput();
                Map<String, String> extractedValues = ParameterExtractor.extract(rawOutput, frozenVarNames);
                if (extractedValues.isEmpty()) {
                    log.warn("ParameterAdjust attempt {}: failed to extract FROZENVAR values", attempt + 1);
                    FixStrategyUtils.recordSolverFailure(ctx, NAME,
                            "NuSMV output did not contain the parameter assignment required by the search.");
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
                            .targetId(template.getTargetId())
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
                    FixStrategyUtils.recordSolverFailure(ctx, NAME,
                            "NuSMV output contained an incomplete parameter assignment.");
                    continue;
                }

                // Step 2e: Forward-verify with modified rules
                if (FixStrategyUtils.forwardVerify(smvGenerator, nusmvExecutor, ctx, modifiedRules, NAME)) {
                    // §5.3: Refine to closest original values
                    refineToClosest(candidateAdjustments, thresholds, extractedValues, allRules, ctx);

                    candidateAdjustments.forEach(adjustment ->
                            adjustment.setDescription(describeParameterAdjustment(adjustment, allRules)));
                    String description = candidateAdjustments.stream()
                            .map(ParameterAdjustment::getDescription)
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
                if (e instanceof cn.edu.nju.Iot_Verify.exception.SmvGenerationException) {
                    String reason = "Parameter candidate generation failed: " + e.getMessage();
                    ctx.addDiagnostic(reason);
                    ctx.recordStrategyGenerationFailure(NAME, reason);
                    return null;
                }
                FixStrategyUtils.recordSolverFailure(ctx, NAME,
                        "Parameter search encountered an execution error: " + e.getMessage());
                // Continue to next attempt — exception may be transient or INVAR-dependent
            } finally {
                FixStrategyUtils.cleanupTempDir(smvFile);
            }
        }

        log.info("ParameterAdjustStrategy: exhausted attempts without finding a fix");
        if (!ctx.isExpired()) {
            FixContext.StrategySearchProgress progress = ctx.strategySearchProgress(NAME);
            if (progress != null && progress.attemptsUsed() >= progress.attemptLimit()) {
                recordBudgetExhausted(ctx);
            }
        }
        return null;
    }

    private static void recordBudgetExhausted(FixContext ctx) {
        FixContext.StrategySearchProgress progress = ctx.strategySearchProgress(NAME);
        int used = progress != null ? progress.attemptsUsed() : 0;
        int limit = progress != null ? progress.attemptLimit() : 0;
        ctx.recordStrategyNoResult(NAME, "SEARCH_BUDGET_EXHAUSTED",
                "Parameter search consumed " + used + " of " + limit
                        + " allowed attempts before it could establish that no repair exists.");
    }

    private SingleParameterSearchResult tryClosestSingleParameterFix(
            List<ParameterAdjustment> adjustmentTemplate,
            List<RuleDto> allRules,
            SpecificationDto violatedSpec,
            List<FaultRuleDto> faultRules,
            int maxAttempts,
            FixContext ctx) {
        Set<Integer> localizedRuleIndices = faultRules.stream()
                .filter(Objects::nonNull)
                .map(FaultRuleDto::getRuleIndex)
                .collect(Collectors.toCollection(LinkedHashSet::new));
        List<ParameterAdjustment> orderedTemplates = new ArrayList<>(adjustmentTemplate);
        orderedTemplates.sort(Comparator.comparingInt(template ->
                localizedRuleIndices.contains(template.getRuleIndex()) ? 0 : 1));

        int attempts = 0;
        for (ParameterAdjustment template : orderedTemplates) {
            if (attempts >= maxAttempts || ctx.isExpired()) break;
            Integer original = safeParseInt(template.getOriginalValue());
            if (original == null) continue;

            LinkedHashSet<Integer> policyHints = numericPolicyHints(
                    violatedSpec, template, allRules, ctx.getDeviceSmvMap());
            Integer verifiedValue = null;
            int verifiedDistance = Integer.MAX_VALUE;

            List<Integer> policyProbes = new ArrayList<>(policyHints.stream()
                    .sorted(Comparator.comparingLong(value -> distance(value, original)))
                    .toList());
            Set<Integer> scheduledPolicyProbes = new LinkedHashSet<>(policyProbes);
            Set<Integer> attemptedPolicyProbes = new HashSet<>();
            for (int probeIndex = 0; probeIndex < policyProbes.size(); probeIndex++) {
                int hint = policyProbes.get(probeIndex);
                if (attempts >= maxAttempts || ctx.isExpired()) break;
                if (hint == original || hint < template.getLowerBound() || hint > template.getUpperBound()) {
                    continue;
                }
                if (!singleParameterCandidatePersistable(template, hint, allRules)) {
                    Integer next = tighteningNeighbor(hint, template.getRelation());
                    if (next != null
                            && next >= template.getLowerBound()
                            && next <= template.getUpperBound()
                            && scheduledPolicyProbes.add(next)) {
                        policyProbes.add(next);
                    }
                    continue;
                }
                attemptedPolicyProbes.add(hint);
                attempts++;
                if (singleParameterForwardVerifies(template, hint, allRules, ctx)) {
                    verifiedValue = hint;
                    verifiedDistance = (int) Math.min(Integer.MAX_VALUE, distance(hint, original));
                    break;
                }
            }

            NearestValueCursor cursor = new NearestValueCursor(
                    original, template.getLowerBound(), template.getUpperBound(), template.getRelation());
            while (attempts < maxAttempts && !ctx.isExpired()) {
                Integer candidate = cursor.next();
                if (candidate == null) break;
                long candidateDistance = distance(candidate, original);
                if (verifiedValue != null && candidateDistance >= verifiedDistance) break;
                if (attemptedPolicyProbes.contains(candidate)) continue;
                if (!singleParameterCandidatePersistable(template, candidate, allRules)) continue;
                attempts++;
                if (singleParameterForwardVerifies(template, candidate, allRules, ctx)) {
                    verifiedValue = candidate;
                    verifiedDistance = (int) Math.min(Integer.MAX_VALUE, candidateDistance);
                }
            }

            if (verifiedValue != null) {
                ParameterAdjustment adjustment = adjustmentWithValue(template, verifiedValue, allRules);
                return new SingleParameterSearchResult(FixSuggestionDto.builder()
                        .strategy(NAME)
                        .description("Adjust parameter: " + adjustment.getDescription())
                        .parameterAdjustments(List.of(adjustment))
                        .verified(true)
                        .build(), attempts);
            }
        }
        return new SingleParameterSearchResult(null, attempts);
    }

    private SingleParameterSearchResult tryCoordinatedPolicyFix(
            List<ParameterAdjustment> adjustmentTemplate,
            List<RuleDto> allRules,
            SpecificationDto violatedSpec,
            List<FaultRuleDto> faultRules,
            FixContext ctx) {
        Set<String> localizedCommandKeys = faultRules.stream()
                .filter(Objects::nonNull)
                .map(FaultRuleDto::getRuleIndex)
                .filter(index -> index != null && index >= 0 && index < allRules.size())
                .map(index -> commandKey(allRules.get(index), ctx.getDeviceSmvMap()))
                .filter(Objects::nonNull)
                .collect(Collectors.toCollection(LinkedHashSet::new));
        if (localizedCommandKeys.isEmpty()) {
            return new SingleParameterSearchResult(null, 0);
        }

        List<ParameterAdjustment> coordinated = new ArrayList<>();
        for (ParameterAdjustment template : adjustmentTemplate) {
            if (template.getRuleIndex() < 0 || template.getRuleIndex() >= allRules.size()) continue;
            String commandKey = commandKey(allRules.get(template.getRuleIndex()), ctx.getDeviceSmvMap());
            if (!localizedCommandKeys.contains(commandKey)) continue;

            Integer original = safeParseInt(template.getOriginalValue());
            if (original == null) continue;
            boolean tightenHigher = ">".equals(template.getRelation()) || ">=".equals(template.getRelation());
            List<Integer> tighteningHints = numericPolicyHints(
                    violatedSpec, template, allRules, ctx.getDeviceSmvMap()).stream()
                    .filter(value -> value >= template.getLowerBound() && value <= template.getUpperBound())
                    .filter(value -> tightenHigher ? value > original : value < original)
                    .toList();
            if (tighteningHints.isEmpty()) continue;
            int selected = tightenHigher
                    ? Collections.max(tighteningHints)
                    : Collections.min(tighteningHints);
            coordinated.add(adjustmentWithValue(template, selected, allRules));
        }
        if (coordinated.size() < 2) {
            return new SingleParameterSearchResult(null, 0);
        }

        List<RuleDto> modifiedRules = FixStrategyUtils.deepCopyRules(allRules);
        coordinated.forEach(adjustment -> applyAdjustment(modifiedRules, adjustment));

        // Equal coordinated boundaries can make redundant rules identical. Move later rules one
        // discrete step farther in the same tightening direction until the Board invariant holds.
        int structuralSteps = 0;
        int maxStructuralSteps = allRules.size() + coordinated.size() + 1;
        while (!FixStrategyUtils.candidateRulesPersistable(modifiedRules)
                && structuralSteps < maxStructuralSteps) {
            boolean advanced = false;
            for (int index = coordinated.size() - 1; index >= 0; index--) {
                ParameterAdjustment adjustment = coordinated.get(index);
                Integer current = safeParseInt(adjustment.getNewValue());
                Integer next = current == null ? null : tighteningNeighbor(current, adjustment.getRelation());
                if (next == null || next < adjustment.getLowerBound() || next > adjustment.getUpperBound()) {
                    continue;
                }
                adjustment.setNewValue(String.valueOf(next));
                adjustment.setDescription(describeParameterAdjustment(adjustment, allRules));
                applyAdjustment(modifiedRules, adjustment);
                structuralSteps++;
                advanced = true;
                if (FixStrategyUtils.candidateRulesPersistable(modifiedRules)) break;
            }
            if (!advanced) {
                return new SingleParameterSearchResult(null, 0);
            }
        }
        if (!FixStrategyUtils.candidateRulesPersistable(modifiedRules)) {
            return new SingleParameterSearchResult(null, 0);
        }

        if (!FixStrategyUtils.forwardVerify(smvGenerator, nusmvExecutor, ctx, modifiedRules, NAME)) {
            return new SingleParameterSearchResult(null, 1);
        }
        String description = coordinated.stream()
                .map(ParameterAdjustment::getDescription)
                .collect(Collectors.joining("; "));
        return new SingleParameterSearchResult(FixSuggestionDto.builder()
                .strategy(NAME)
                .description("Adjust parameters together: " + description)
                .parameterAdjustments(coordinated)
                .verified(true)
                .build(), 1);
    }

    private static void applyAdjustment(List<RuleDto> rules, ParameterAdjustment adjustment) {
        rules.get(adjustment.getRuleIndex()).getConditions()
                .get(adjustment.getConditionIndex()).setValue(adjustment.getNewValue());
    }

    private static String commandKey(
            RuleDto rule, Map<String, DeviceSmvData> deviceSmvMap) {
        return FixStrategyUtils.commandFingerprint(rule, deviceSmvMap);
    }

    private boolean singleParameterForwardVerifies(
            ParameterAdjustment template, int value, List<RuleDto> allRules, FixContext ctx) {
        List<RuleDto> modifiedRules = FixStrategyUtils.deepCopyRules(allRules);
        modifiedRules.get(template.getRuleIndex()).getConditions()
                .get(template.getConditionIndex()).setValue(String.valueOf(value));
        return FixStrategyUtils.forwardVerify(smvGenerator, nusmvExecutor, ctx, modifiedRules, NAME);
    }

    private static boolean singleParameterCandidatePersistable(
            ParameterAdjustment template, int value, List<RuleDto> allRules) {
        List<RuleDto> modifiedRules = FixStrategyUtils.deepCopyRules(allRules);
        modifiedRules.get(template.getRuleIndex()).getConditions()
                .get(template.getConditionIndex()).setValue(String.valueOf(value));
        return FixStrategyUtils.candidateRulesPersistable(modifiedRules);
    }

    private static Integer tighteningNeighbor(int value, String relation) {
        String normalized = SmvRelationUtils.normalizeRelation(relation);
        if ((">".equals(normalized) || ">=".equals(normalized)) && value < Integer.MAX_VALUE) {
            return value + 1;
        }
        if (("<".equals(normalized) || "<=".equals(normalized)) && value > Integer.MIN_VALUE) {
            return value - 1;
        }
        return null;
    }

    private static ParameterAdjustment adjustmentWithValue(
            ParameterAdjustment template, int value, List<RuleDto> allRules) {
        ParameterAdjustment adjustment = ParameterAdjustment.builder()
                .targetId(template.getTargetId())
                .ruleIndex(template.getRuleIndex())
                .conditionIndex(template.getConditionIndex())
                .attribute(template.getAttribute())
                .relation(template.getRelation())
                .originalValue(template.getOriginalValue())
                .newValue(String.valueOf(value))
                .lowerBound(template.getLowerBound())
                .upperBound(template.getUpperBound())
                .build();
        adjustment.setDescription(describeParameterAdjustment(adjustment, allRules));
        return adjustment;
    }

    private static LinkedHashSet<Integer> numericPolicyHints(
            SpecificationDto violatedSpec,
            ParameterAdjustment template,
            List<RuleDto> allRules,
            Map<String, DeviceSmvData> deviceSmvMap) {
        LinkedHashSet<Integer> result = new LinkedHashSet<>();
        if (violatedSpec == null) return result;
        RuleDto.Condition adjustedCondition = conditionAt(
                allRules, template.getRuleIndex(), template.getConditionIndex());
        if (adjustedCondition == null) return result;
        List<SpecConditionDto> conditions = new ArrayList<>();
        if (violatedSpec.getAConditions() != null) conditions.addAll(violatedSpec.getAConditions());
        if (violatedSpec.getIfConditions() != null) conditions.addAll(violatedSpec.getIfConditions());
        if (violatedSpec.getThenConditions() != null) conditions.addAll(violatedSpec.getThenConditions());
        for (SpecConditionDto condition : conditions) {
            if (condition == null || !Objects.equals(template.getAttribute(), condition.getKey())) continue;
            if (!sameNumericDomain(adjustedCondition, condition, deviceSmvMap)) continue;
            Integer value = safeParseInt(condition.getValue());
            if (value != null) addPolicyBoundaryHints(result, value);
        }
        return result;
    }

    private static void addPolicyBoundaryHints(Set<Integer> hints, int value) {
        if (value > Integer.MIN_VALUE) hints.add(value - 1);
        hints.add(value);
        if (value < Integer.MAX_VALUE) hints.add(value + 1);
    }

    private static RuleDto.Condition conditionAt(
            List<RuleDto> rules, int ruleIndex, int conditionIndex) {
        if (rules == null || ruleIndex < 0 || ruleIndex >= rules.size()) return null;
        RuleDto rule = rules.get(ruleIndex);
        if (rule == null || rule.getConditions() == null
                || conditionIndex < 0 || conditionIndex >= rule.getConditions().size()) return null;
        return rule.getConditions().get(conditionIndex);
    }

    private static boolean sameNumericDomain(
            RuleDto.Condition adjustedCondition,
            SpecConditionDto policyCondition,
            Map<String, DeviceSmvData> deviceSmvMap) {
        DeviceSmvData adjustedDevice = DeviceReferenceResolver.resolve(
                adjustedCondition.getDeviceName(), deviceSmvMap);
        DeviceSmvData policyDevice = DeviceReferenceResolver.resolve(
                policyCondition.getDeviceId(), deviceSmvMap);
        if (adjustedDevice == null || policyDevice == null) return false;
        if (Objects.equals(adjustedDevice.getVarName(), policyDevice.getVarName())) return true;
        String attribute = adjustedCondition.getAttribute();
        return attribute != null
                && adjustedDevice.getEnvVariables() != null
                && policyDevice.getEnvVariables() != null
                && adjustedDevice.getEnvVariables().containsKey(attribute)
                && policyDevice.getEnvVariables().containsKey(attribute);
    }

    static long distance(int value, int original) {
        return Math.abs((long) value - original);
    }

    static int[] refinementWindow(
            int original, long bestDistance, int lowerBound, int upperBound) {
        long lower = Math.max((long) lowerBound, (long) original - bestDistance + 1L);
        long upper = Math.min((long) upperBound, (long) original + bestDistance - 1L);
        return new int[]{(int) lower, (int) upper};
    }

    private static final class NearestValueCursor {
        private final int original;
        private final int lowerBound;
        private final int upperBound;
        private final boolean preferHigher;
        private long lower;
        private long upper;

        private NearestValueCursor(int original, int lowerBound, int upperBound, String relation) {
            this.original = original;
            this.lowerBound = lowerBound;
            this.upperBound = upperBound;
            String normalized = SmvRelationUtils.normalizeRelation(relation);
            this.preferHigher = ">".equals(normalized) || ">=".equals(normalized);
            this.lower = Math.min((long) upperBound, (long) original - 1);
            this.upper = Math.max((long) lowerBound, (long) original + 1);
        }

        private Integer next() {
            boolean hasLower = lower >= lowerBound && lower <= upperBound;
            boolean hasUpper = upper >= lowerBound && upper <= upperBound;
            if (!hasLower && !hasUpper) return null;
            long lowerDistance = hasLower ? distance((int) lower, original) : Long.MAX_VALUE;
            long upperDistance = hasUpper ? distance((int) upper, original) : Long.MAX_VALUE;
            if (upperDistance < lowerDistance || (preferHigher && upperDistance == lowerDistance)) {
                return (int) upper++;
            }
            return (int) lower--;
        }
    }

    // ======================== §5.3: Refine to closest original ========================

    static String describeParameterAdjustment(ParameterAdjustment adjustment, List<RuleDto> allRules) {
        String base = describeRule(allRules, adjustment.getRuleIndex())
                + ": adjust parameter condition " + (adjustment.getConditionIndex() + 1)
                + " (" + adjustment.getAttribute() + " " + adjustment.getRelation() + " "
                + adjustment.getOriginalValue() + " -> " + adjustment.getNewValue() + ")";
        Integer newVal = safeParseInt(adjustment.getNewValue());
        String relation = SmvRelationUtils.normalizeRelation(adjustment.getRelation());
        if (newVal != null && ((">".equals(relation) && newVal == adjustment.getUpperBound())
                || ("<".equals(relation) && newVal == adjustment.getLowerBound()))) {
            base += " (strict boundary makes the rule unreachable)";
        }
        return base;
    }

    private static String describeParameterTarget(
            List<RuleDto> allRules,
            int ruleIndex,
            int conditionIndex,
            RuleDto.Condition condition,
            String normalizedRelation) {
        return describeRule(allRules, ruleIndex)
                + ": parameter condition " + (conditionIndex + 1)
                + " (" + condition.getAttribute() + " " + normalizedRelation + " "
                + condition.getValue().trim() + ")";
    }

    private static String describeRule(List<RuleDto> rules, int ruleIndex) {
        if (rules != null && ruleIndex >= 0 && ruleIndex < rules.size()) {
            RuleDto rule = rules.get(ruleIndex);
            if (rule != null && rule.getRuleString() != null && !rule.getRuleString().isBlank()) {
                return "'" + rule.getRuleString() + "'";
            }
        }
        return "Rule #" + (ruleIndex + 1);
    }

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
            long bestDist = distance(best, original);

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
                    if (FixStrategyUtils.forwardVerify(smvGenerator, nusmvExecutor, ctx, testRules, NAME)) {
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

                int[] window = refinementWindow(
                        original, bestDist, paramInfo.getLowerBound(), paramInfo.getUpperBound());
                int L = window[0];
                int U = window[1];
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
                            if (FixStrategyUtils.forwardVerify(smvGenerator, nusmvExecutor, ctx, verifyRules, NAME)) {
                                best = cand;
                                bestDist = distance(cand, original);
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
            SmvGenerator.GenerateResult genResult =
                    FixStrategyUtils.generateParameterizedResolved(
                            smvGenerator, ctx, rulesWithOtherParamsApplied, config);
            if (genResult == null) return RefineResult.error();
            if (!FixStrategyUtils.candidateModelComplete(genResult, ctx, NAME)) return RefineResult.error();
            smvFile = genResult.smvFile();

            NusmvResult result = FixStrategyUtils.executeWithinDeadline(nusmvExecutor, smvFile, ctx);
            if (!result.isSuccess()) {
                log.warn("nusmvSolveForRefine: execution failed: {}", result.getErrorMessage());
                FixStrategyUtils.recordSolverFailure(ctx, NAME,
                        "NuSMV failed while refining a verified parameter repair.");
                return RefineResult.error();
            }

            List<SpecCheckResult> specResults = result.getSpecResults();
            if (specResults == null || specResults.isEmpty()) {
                FixStrategyUtils.recordSolverFailure(ctx, NAME,
                        "NuSMV returned no usable specification result during parameter refinement.");
                return RefineResult.error();
            }

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
                FixStrategyUtils.recordSolverFailure(ctx, NAME,
                        "NuSMV output did not contain the parameter value required for refinement.");
                return RefineResult.error();
            }

            int cand;
            try {
                cand = Integer.parseInt(valueStr);
            } catch (NumberFormatException e) {
                log.warn("nusmvSolveForRefine: non-integer value '{}' for {}", valueStr, narrowed.getFrozenVarName());
                FixStrategyUtils.recordSolverFailure(ctx, NAME,
                        "NuSMV output contained a non-integer parameter value during refinement.");
                return RefineResult.error();
            }

            // Bounds check (defensive — NuSMV should respect FROZENVAR range, but guard against edge cases)
            if (cand < narrowedLower || cand > narrowedUpper) {
                log.warn("nusmvSolveForRefine: candidate {} outside [{},{}], treating as error",
                        cand, narrowedLower, narrowedUpper);
                FixStrategyUtils.recordSolverFailure(ctx, NAME,
                        "NuSMV returned a parameter value outside the requested refinement bounds.");
                return RefineResult.error();
            }

            return RefineResult.candidate(cand);

        } catch (Exception e) {
            log.warn("nusmvSolveForRefine: exception: {}", e.getMessage(), e);
            if (!(e instanceof cn.edu.nju.Iot_Verify.exception.SmvGenerationException)) {
                FixStrategyUtils.recordSolverFailure(ctx, NAME,
                        "Parameter refinement encountered an execution error: " + e.getMessage());
            }
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
            smv = DeviceReferenceResolver.resolve(deviceId, deviceSmvMap);
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
            DeviceManifest.InternalVariable envVar = smv.getEnvVariables().get(attr);
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
