package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixContext;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.FixStrategy;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;
import java.util.stream.Collectors;

/**
 * DisableFixStrategy: attempts to fix a specification violation by finding a minimal set of
 * fault rules to disable, then re-verifying with NuSMV.
 *
 * Algorithm:
 * 1. Start with disabling 1 fault rule, then try combinations of 2, 3, ... up to max.
 * 2. For each candidate set, regenerate the NuSMV model without the disabled rules and re-verify.
 * 3. Return the first combination where all specs pass.
 */
@Slf4j
@Component
@RequiredArgsConstructor
public class DisableFixStrategy implements FixStrategy {

    private static final String NAME = "disable";

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

        // Deduplicate fault rule indices
        List<Integer> faultIndices = faultRules.stream()
                .map(FaultRuleDto::getRuleIndex)
                .distinct()
                .collect(Collectors.toList());

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
                        .map(idx -> idx < allRules.size() && allRules.get(idx).getRuleString() != null
                                ? "Rule " + idx + ": " + allRules.get(idx).getRuleString()
                                : "Rule " + idx)
                        .collect(Collectors.toList());

                return FixSuggestionDto.builder()
                        .strategy(NAME)
                        .description("Disable " + combo.size() + " rule(s): "
                                + String.join(", ", ruleDescriptions))
                        .disabledRuleIndices(combo)
                        .verified(true)
                        .build();
            }
        }

        log.info("DisableFixStrategy exhausted {} attempts without finding a fix", attempts);
        return null;
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

            List<Integer> combo = new ArrayList<>();
            for (int idx : result) combo.add(faultIndices.get(idx));

            List<RuleDto> remainingRules = removeRulesByIndex(allRules, combo);
            log.info("Fix attempt {}/{}: disabling rule indices {} ({} rules remaining)",
                    attempts, maxAttempts, combo, remainingRules.size());

            boolean allPass = FixStrategyUtils.forwardVerify(smvGenerator, nusmvExecutor, ctx, remainingRules);
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
}
