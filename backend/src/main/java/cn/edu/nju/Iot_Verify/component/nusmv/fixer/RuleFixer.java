package cn.edu.nju.Iot_Verify.component.nusmv.fixer;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.localize.FaultLocalizer;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.time.Instant;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * RuleFixer: orchestrates fault localization and fix strategy execution.
 *
 * <p>Default strategy order follows Salus paper §5:
 * parameter (§5.1) → condition (§5.2) → disable (fallback).</p>
 */
@Slf4j
@Component
public class RuleFixer {

    private static final List<String> DEFAULT_STRATEGIES = List.of("parameter", "condition", "disable");

    private final FaultLocalizer faultLocalizer;
    private final Map<String, FixStrategy> strategyRegistry;
    private final FixConfig fixConfig;

    public RuleFixer(FaultLocalizer faultLocalizer, List<FixStrategy> strategies, FixConfig fixConfig) {
        this.faultLocalizer = faultLocalizer;
        this.fixConfig = fixConfig;
        this.strategyRegistry = strategies.stream()
                .collect(Collectors.toMap(
                        FixStrategy::name,
                        Function.identity(),
                        (existing, duplicate) -> {
                            log.warn("Duplicate FixStrategy name '{}': keeping {}, ignoring {}",
                                    existing.name(), existing.getClass().getSimpleName(),
                                    duplicate.getClass().getSimpleName());
                            return existing;
                        }));
    }

    /**
     * Only localize faults (no fix attempt).
     */
    public List<FaultRuleDto> localizeFaults(List<TraceStateDto> states,
                                              List<RuleDto> rules,
                                              Map<String, DeviceSmvData> deviceSmvMap) {
        return faultLocalizer.localize(states, rules, deviceSmvMap);
    }

    /**
     * Full fix pipeline: localize faults, then attempt fix strategies.
     */
    public FixResultDto fix(Long traceId,
                            String violatedSpecId,
                            List<TraceStateDto> states,
                            List<RuleDto> rules,
                            List<DeviceVerificationDto> devices,
                            List<SpecificationDto> specs,
                            Map<String, DeviceSmvData> deviceSmvMap,
                            Long userId,
                            boolean isAttack, int intensity, boolean enablePrivacy,
                            List<String> strategies,
                            int maxAttempts,
                            Map<String, PreferredRange> preferredRanges) {

        // Step 1: Fault localization
        List<FaultRuleDto> faultRules = faultLocalizer.localize(states, rules, deviceSmvMap);
        log.info("Fault localization: found {} fault rule(s) for trace {}", faultRules.size(), traceId);

        if (faultRules.isEmpty()) {
            String emptyReason = (states == null || states.size() < 2)
                    ? "Counterexample trace has fewer than 2 states; fault localization requires at least 2 states."
                    : "No fault rules found in counterexample trace. "
                      + "The violation may be caused by device transitions or environment conditions, "
                      + "not by user-defined rules.";
            return FixResultDto.builder()
                    .traceId(traceId)
                    .violatedSpecId(violatedSpecId)
                    .faultRules(faultRules)
                    .suggestions(List.of())
                    .fixable(false)
                    .summary(emptyReason)
                    .build();
        }

        // Resolve violatedSpecIndex from violatedSpecId
        int violatedSpecIndex = resolveSpecIndex(violatedSpecId, specs);

        // Build shared context for all strategies
        FixContext ctx = FixContext.builder()
                .faultRules(faultRules)
                .allRules(rules)
                .devices(devices)
                .specs(specs)
                .deviceSmvMap(deviceSmvMap)
                .violatedSpecIndex(violatedSpecIndex)
                .userId(userId)
                .isAttack(isAttack)
                .intensity(intensity)
                .enablePrivacy(enablePrivacy)
                .maxAttempts(maxAttempts)
                .preferredRanges(preferredRanges)
                .deadline(Instant.now().plusMillis(fixConfig.getFixTimeoutMs()))
                .build();

        // Step 2: Attempt fix strategies via registry
        List<FixSuggestionDto> suggestions = new ArrayList<>();
        List<String> effectiveStrategies = (strategies != null && !strategies.isEmpty())
                ? strategies : DEFAULT_STRATEGIES;

        for (String strategyName : effectiveStrategies) {
            if (ctx.isExpired()) {
                log.warn("Fix deadline expired before strategy '{}', skipping remaining strategies", strategyName);
                break;
            }
            FixStrategy strategy = strategyRegistry.get(strategyName);
            if (strategy == null) {
                log.info("Unsupported fix strategy '{}', skipping", strategyName);
                continue;
            }
            // Skip strategies that need a valid violatedSpecIndex when it's missing
            if (violatedSpecIndex < 0 && strategy.requiresViolatedSpec()) {
                log.info("Skipping '{}' strategy: no valid violated spec index", strategyName);
                continue;
            }
            FixSuggestionDto suggestion = strategy.tryFix(ctx);
            if (suggestion != null) {
                suggestions.add(suggestion);
            }
        }

        boolean fixable = !suggestions.isEmpty();
        StringBuilder summaryBuilder = new StringBuilder();
        if (fixable) {
            summaryBuilder.append("Found ").append(suggestions.size())
                    .append(" fix suggestion(s) for ").append(faultRules.size()).append(" fault rule(s).");
        } else {
            summaryBuilder.append(faultRules.size())
                    .append(" fault rule(s) identified but no fix strategy resolved the violation.");
        }

        if (ctx.isExpired()) {
            summaryBuilder.append(" (fix timed out; results may be partial)");
        }

        // UX-4: Append reason if violatedSpecId could not be resolved
        if (violatedSpecIndex < 0) {
            summaryBuilder.append(" (violatedSpecId '").append(violatedSpecId)
                    .append("' could not be resolved; parameter and condition strategies were skipped)");
        }

        // UX-2: Detect unused preferredRange keys
        List<String> unusedKeys = null;
        if (preferredRanges != null && !preferredRanges.isEmpty()) {
            Set<String> usedKeys = new LinkedHashSet<>();
            for (FixSuggestionDto s : suggestions) {
                if (s.getParameterAdjustments() != null) {
                    for (var adj : s.getParameterAdjustments()) {
                        usedKeys.add("r" + adj.getRuleIndex() + "_c" + adj.getConditionIndex());
                    }
                }
            }
            unusedKeys = new ArrayList<>();
            for (String key : preferredRanges.keySet()) {
                if (!usedKeys.contains(key)) {
                    unusedKeys.add(key);
                }
            }
            if (unusedKeys.isEmpty()) {
                unusedKeys = null;
            } else {
                summaryBuilder.append(" Note: preferredRanges keys ")
                        .append(unusedKeys).append(" were not used in any parameter fix suggestion.");
            }
        }

        return FixResultDto.builder()
                .traceId(traceId)
                .violatedSpecId(violatedSpecId)
                .faultRules(faultRules)
                .suggestions(suggestions)
                .fixable(fixable)
                .summary(summaryBuilder.toString())
                .unusedPreferredRangeKeys(unusedKeys)
                .build();
    }

    private int resolveSpecIndex(String violatedSpecId, List<SpecificationDto> specs) {
        if (violatedSpecId == null || specs == null) return -1;
        for (int i = 0; i < specs.size(); i++) {
            SpecificationDto spec = specs.get(i);
            if (spec != null && violatedSpecId.equals(spec.getId())) {
                return i;
            }
        }
        // Try matching by numeric index (violatedSpecId might be "0", "1", etc.)
        try {
            int idx = Integer.parseInt(violatedSpecId);
            if (idx >= 0 && idx < specs.size()) return idx;
        } catch (NumberFormatException ignored) {}
        log.warn("Could not resolve violatedSpecId '{}' to spec index", violatedSpecId);
        return -1;
    }
}
