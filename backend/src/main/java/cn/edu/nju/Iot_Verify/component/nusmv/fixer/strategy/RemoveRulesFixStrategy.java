package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixContext;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixStrategy;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.math.BigInteger;
import java.util.*;
import java.util.stream.Collectors;

/**
 * RemoveRulesFixStrategy: attempts to fix a specification violation by finding a minimal set of
 * fault rules to remove, then re-verifying with NuSMV.
 *
 * Algorithm:
 * 1. Start with disabling 1 fault rule, then try combinations of 2, 3, ... up to max.
 * 2. For each candidate set, regenerate the NuSMV model without the disabled rules and re-verify.
 * 3. Return the first combination where all specs pass.
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class RemoveRulesFixStrategy implements FixStrategy {

    private static final String NAME = "remove";

    private final SmvGenerator smvGenerator;
    private final NusmvExecutor nusmvExecutor;

    @Override
    public String name() {
        return NAME;
    }

    @Override
    public boolean requiresViolatedSpec() {
        return false;
    }

    @Override
    public FixSuggestionDto tryFix(FixContext ctx) {
        List<FaultRuleDto> faultRules = ctx.getFaultRules();
        List<RuleDto> allRules = ctx.getAllRules();
        int maxAttempts = ctx.getMaxAttempts() > 0 ? ctx.getMaxAttempts() : 20;

        if (faultRules == null || faultRules.isEmpty()) {
            return null;
        }

        // A lower-priority rule may be dormant in this particular trace and take over after the
        // localized rule is removed. Include the same spec-related expansion used by the other
        // strategies so minimal removal combinations can account for those backup automations.
        Set<Integer> candidateIndices = new LinkedHashSet<>();
        int violatedSpecIndex = ctx.getViolatedSpecIndex();
        if (ctx.getSpecs() != null && violatedSpecIndex >= 0
                && violatedSpecIndex < ctx.getSpecs().size()) {
            SpecificationDto violatedSpec = ctx.getSpecs().get(violatedSpecIndex);
            candidateIndices.addAll(FixStrategyUtils.expandRuleIndices(
                    faultRules, allRules, violatedSpec, ctx.getDeviceSmvMap()));
        } else {
            faultRules.stream()
                    .map(FaultRuleDto::getRuleIndex)
                    .filter(index -> index != null && index >= 0 && index < allRules.size())
                    .forEach(candidateIndices::add);
        }
        List<Integer> faultIndices = new ArrayList<>(candidateIndices);
        if (faultIndices.isEmpty()) {
            return null;
        }
        ctx.initializeStrategySearch(NAME, maxAttempts);

        int attempts = 0;

        // Try disabling increasing numbers of rules (1, 2, 3, ...)
        for (int count = 1; count <= faultIndices.size() && attempts < maxAttempts; count++) {
            int[] result = new int[count];
            attempts = tryCombinations(faultIndices, result, 0, 0, count,
                    ctx, allRules, attempts, maxAttempts);
            if (attempts < 0) {
                // Negative means a fix was found; decode the combo from result array
                List<Integer> combo = new ArrayList<>();
                for (int idx : result) combo.add(idx);
                List<String> ruleDescriptions = combo.stream()
                        .map(idx -> describeRule(allRules, idx))
                        .collect(Collectors.toList());

                return FixSuggestionDto.builder()
                        .strategy(NAME)
                        .description("Permanently remove " + combo.size() + " automation rule(s): "
                                + String.join(", ", ruleDescriptions))
                        .removedRuleIndices(combo)
                        .removedRuleDescriptions(ruleDescriptions)
                        .verified(true)
                        .build();
            }
        }

        log.info("RemoveRulesFixStrategy exhausted {} attempts without finding a fix", attempts);
        if (!ctx.isExpired() && combinationCount(faultIndices.size())
                .compareTo(BigInteger.valueOf(attempts)) > 0) {
            ctx.recordStrategyNoResult(NAME, "SEARCH_BUDGET_EXHAUSTED",
                    "Rule-removal search consumed " + attempts + " of " + maxAttempts
                            + " allowed attempts before all candidate combinations were checked.");
        }
        return null;
    }

    private static BigInteger combinationCount(int candidateCount) {
        return candidateCount <= 0
                ? BigInteger.ZERO
                : BigInteger.ONE.shiftLeft(candidateCount).subtract(BigInteger.ONE);
    }

    /**
     * Lazy DFS combination generator + verifier. Returns negative if fix found (combo stored in result[]),
     * otherwise returns updated attempts count.
     */
    private int tryCombinations(List<Integer> faultIndices, int[] result, int start, int depth, int count,
                                FixContext ctx, List<RuleDto> allRules,
                                int attempts, int maxAttempts) {
        if (depth == count) {
            if (attempts >= maxAttempts || ctx.isExpired()) return attempts;
            attempts++;
            ctx.addStrategyAttempts(NAME, 1);

            List<Integer> combo = new ArrayList<>();
            for (int idx : result) combo.add(faultIndices.get(idx));

            List<RuleDto> remainingRules = removeRulesByIndex(allRules, combo);
            log.info("Fix attempt {}/{}: removing rule indices {} ({} rules remaining)",
                    attempts, maxAttempts, combo, remainingRules.size());

            boolean allPass = FixStrategyUtils.forwardVerify(
                    smvGenerator, nusmvExecutor, ctx, remainingRules, NAME);
            if (allPass) {
                // Store the winning combo indices back into result for caller
                for (int i = 0; i < count; i++) result[i] = faultIndices.get(result[i]);
                return -1; // signal: fix found
            }
            return attempts;
        }

        for (int i = start; i < faultIndices.size(); i++) {
            if (attempts >= maxAttempts || ctx.isExpired()) return attempts;
            result[depth] = i;
            attempts = tryCombinations(faultIndices, result, i + 1, depth + 1, count,
                    ctx, allRules, attempts, maxAttempts);
            if (attempts < 0) return attempts; // propagate fix-found signal
        }
        return attempts;
    }

    private List<RuleDto> removeRulesByIndex(List<RuleDto> allRules, List<Integer> indicesToRemove) {
        Set<Integer> removeSet = new HashSet<>(indicesToRemove);
        List<RuleDto> remaining = new ArrayList<>();
        for (int i = 0; i < allRules.size(); i++) {
            if (!removeSet.contains(i)) {
                remaining.add(allRules.get(i));
            }
        }
        return remaining;
    }

    private static String describeRule(List<RuleDto> rules, int ruleIndex) {
        if (rules != null && ruleIndex >= 0 && ruleIndex < rules.size()) {
            RuleDto rule = rules.get(ruleIndex);
            if (rule != null && rule.getRuleString() != null && !rule.getRuleString().isBlank()) {
                return rule.getRuleString().trim();
            }
        }
        return "Unnamed automation rule";
    }
}
