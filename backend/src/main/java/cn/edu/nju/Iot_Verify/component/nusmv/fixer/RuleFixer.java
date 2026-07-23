package cn.edu.nju.Iot_Verify.component.nusmv.fixer;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.localize.FaultLocalizer;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixStrategyAttemptDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRangeSelection;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.time.Instant;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

/**
 * RuleFixer: orchestrates fault localization and fix strategy execution.
 *
 * <p>Default strategy order follows Salus paper §5:
 * parameter (§5.1) → condition (§5.2) → permanent rule removal (fallback).</p>
 */
@Slf4j
@Component
public class RuleFixer {

    private static final List<String> DEFAULT_STRATEGIES = List.of("parameter", "condition", "remove");

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
                            AttackScenarioDto attackScenario,
                            boolean enablePrivacy,
                            List<String> strategies,
                            int maxAttempts,
                            Map<String, PreferredRange> preferredRanges) {
        return fix(traceId, violatedSpecId, states, rules, devices, List.of(), specs, deviceSmvMap,
                userId, attackScenario, enablePrivacy, strategies, maxAttempts, preferredRanges);
    }

    public FixResultDto fix(Long traceId,
                            String violatedSpecId,
                            List<TraceStateDto> states,
                            List<RuleDto> rules,
                            List<DeviceVerificationDto> devices,
                            List<BoardEnvironmentVariableDto> environmentVariables,
                            List<SpecificationDto> specs,
                            Map<String, DeviceSmvData> deviceSmvMap,
                            Long userId,
                            AttackScenarioDto attackScenario,
                            boolean enablePrivacy,
                            List<String> strategies,
                            int maxAttempts,
                            Map<String, PreferredRange> preferredRanges) {

        AttackScenarioDto safeAttackScenario = Objects.requireNonNull(
                attackScenario, "attackScenario is required");
        // Step 1: Fault localization
        List<FaultRuleDto> faultRules = faultLocalizer.localize(states, rules, deviceSmvMap);
        log.info("Fault localization: found {} fault rule(s) for trace {}", faultRules.size(), traceId);
        if (strategies != null && strategies.isEmpty()) {
            throw new IllegalArgumentException(
                    "strategies must be non-empty when provided; use null for the default order");
        }
        List<String> effectiveStrategies = strategies != null ? strategies : DEFAULT_STRATEGIES;

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
                    .strategyAttempts(effectiveStrategies.stream()
                            .map(strategy -> attempt(strategy, "SKIPPED_NO_FAULT_RULES",
                                    "No user-defined fault rule was localized, so this strategy was not run."))
                            .toList())
                    .fixable(false)
                    .sourceModelComplete(true)
                    .summary(emptyReason)
                    .warnings(List.of())
                    .build();
        }

        // Resolve violatedSpecIndex from violatedSpecId
        int violatedSpecIndex = resolveSpecIndex(violatedSpecId, specs);

        // Build shared context for all strategies
        FixContext ctx = FixContext.builder()
                .traceId(traceId)
                .faultRules(faultRules)
                .allRules(rules)
                .devices(devices)
                .environmentVariables(environmentVariables == null ? List.of() : environmentVariables)
                .specs(specs)
                .deviceSmvMap(deviceSmvMap)
                .violatedSpecIndex(violatedSpecIndex)
                .userId(userId)
                .attackScenario(safeAttackScenario)
                .enablePrivacy(enablePrivacy)
                .maxAttempts(maxAttempts)
                .preferredRanges(preferredRanges)
                .counterexampleInitialState(states == null || states.isEmpty() ? null : states.get(0))
                .requireCounterexampleReplay(true)
                .deadline(Instant.now().plusMillis(fixConfig.getFixTimeoutMs()))
                .build();

        // Step 2: Attempt fix strategies via registry
        List<FixSuggestionDto> suggestions = new ArrayList<>();
        List<FixStrategyAttemptDto> strategyAttempts = new ArrayList<>();

        for (int strategyIndex = 0; strategyIndex < effectiveStrategies.size(); strategyIndex++) {
            String strategyName = effectiveStrategies.get(strategyIndex);
            if (ctx.isExpired()) {
                log.warn("Fix deadline expired before strategy '{}', skipping remaining strategies", strategyName);
                for (int skippedIndex = strategyIndex; skippedIndex < effectiveStrategies.size(); skippedIndex++) {
                    strategyAttempts.add(attempt(effectiveStrategies.get(skippedIndex), "SKIPPED_TIMEOUT",
                            "The automatic-fix time limit expired before this strategy could run."));
                }
                break;
            }
            FixStrategy strategy = strategyRegistry.get(strategyName);
            if (strategy == null) {
                log.info("Unsupported fix strategy '{}', skipping", strategyName);
                strategyAttempts.add(attempt(strategyName, "SKIPPED_UNSUPPORTED",
                        "The requested strategy is not supported by this server."));
                continue;
            }
            // Skip strategies that need a valid violatedSpecIndex when it's missing
            if (violatedSpecIndex < 0 && strategy.requiresViolatedSpec()) {
                log.info("Skipping '{}' strategy: no valid violated spec index", strategyName);
                strategyAttempts.add(attempt(strategyName, "SKIPPED_NO_SPEC",
                        "The violated specification could not be resolved from the trace context."));
                continue;
            }
            ctx.clearStrategyGenerationFailure(strategyName);
            ctx.clearStrategySolverFailure(strategyName);
            ctx.clearStrategyNoResult(strategyName);
            FixSuggestionDto suggestion = strategy.tryFix(ctx);
            if (suggestion != null) {
                suggestions.add(suggestion);
                strategyAttempts.add(attempt(strategyName,
                        suggestion.isVerified() ? "VERIFIED" : "NOT_VERIFIED",
                        suggestion.isVerified()
                                ? "A concrete suggestion passed forward verification on the complete generated model."
                                : "A candidate was generated but did not pass forward verification.", ctx));
            } else if (ctx.isExpired()) {
                strategyAttempts.add(attempt(strategyName, "TIMED_OUT",
                        "The automatic-fix time limit expired while this strategy was running; its search was incomplete.", ctx));
            } else if (ctx.strategyGenerationFailure(strategyName) != null) {
                strategyAttempts.add(attempt(strategyName, "FAILED_MODEL_GENERATION",
                        ctx.strategyGenerationFailure(strategyName), ctx));
            } else if (ctx.strategySolverFailure(strategyName) != null) {
                strategyAttempts.add(attempt(strategyName, "FAILED_SOLVER_EXECUTION",
                        ctx.strategySolverFailure(strategyName), ctx));
            } else if (ctx.strategyNoResult(strategyName) != null) {
                FixContext.StrategyNoResult noResult = ctx.strategyNoResult(strategyName);
                strategyAttempts.add(attempt(strategyName, noResult.status(), noResult.reason(), ctx));
            } else {
                strategyAttempts.add(attempt(strategyName, "NO_VERIFIED_SUGGESTION",
                        "The strategy was attempted but produced no suggestion that passed forward verification.", ctx));
            }
        }

        boolean fixable = suggestions.stream().anyMatch(FixSuggestionDto::isVerified);
        StringBuilder summaryBuilder = new StringBuilder();
        if (fixable) {
            summaryBuilder.append("Found ").append(suggestions.size())
                    .append(" fix suggestion(s) for ").append(faultRules.size()).append(" fault rule(s).");
        } else {
            summaryBuilder.append(faultRules.size()).append(" fault rule(s) identified. ");
            if (ctx.isExpired()) {
                summaryBuilder.append("The requested strategy search was incomplete because the fix deadline expired.");
            } else {
                summaryBuilder.append("No requested strategy produced a verified suggestion.");
            }
        }

        if (ctx.isExpired()) {
            summaryBuilder.append(" (fix timed out; results may be partial)");
        }

        // Keep the persistence id out of ordinary feedback; it does not help the user repair the model.
        if (violatedSpecIndex < 0) {
            summaryBuilder.append(" (the violated specification could not be matched to the saved verification "
                    + "snapshot; parameter and condition strategies were skipped)");
        }

        // A selection is used when it matches an eligible target, regardless of whether that
        // constrained search eventually produces a verified suggestion.
        List<PreferredRangeSelection> unusedSelections = new ArrayList<>();
        if (preferredRanges != null && !preferredRanges.isEmpty()) {
            Set<String> matchedTargetIds = ctx.matchedPreferredRangeTargetIdsSnapshot();
            for (Map.Entry<String, PreferredRange> entry : preferredRanges.entrySet()) {
                String targetId = entry.getKey();
                PreferredRange range = entry.getValue();
                if (!matchedTargetIds.contains(targetId)
                        && PreferredRangeSelection.isValidTargetId(targetId) && range != null) {
                    unusedSelections.add(PreferredRangeSelection.builder()
                            .targetId(targetId)
                            .lower(range.getLower())
                            .upper(range.getUpper())
                            .build());
                }
            }
            if (!unusedSelections.isEmpty()) {
                summaryBuilder.append(" Note: some preferred range selections matched no eligible parameter target.");
            }
        }

        List<String> warnings = ctx.diagnosticsSnapshot();
        if (ctx.isExpired()) {
            warnings = new ArrayList<>(warnings);
            warnings.add("The automatic-fix time limit expired; some requested strategies were not attempted.");
        }

        return FixResultDto.builder()
                .traceId(traceId)
                .violatedSpecId(violatedSpecId)
                .faultRules(faultRules)
                .suggestions(suggestions)
                .strategyAttempts(strategyAttempts)
                .fixable(fixable)
                .sourceModelComplete(true)
                .summary(summaryBuilder.toString())
                .warnings(warnings)
                .parameterTargets(ctx.parameterTargetsSnapshot())
                .unusedPreferredRangeSelections(unusedSelections)
                .build();
    }

    private static FixStrategyAttemptDto attempt(String strategy, String status, String reason) {
        return attempt(strategy, status, reason, null);
    }

    private static FixStrategyAttemptDto attempt(
            String strategy, String status, String reason, FixContext ctx) {
        FixContext.StrategySearchProgress progress = ctx != null
                ? ctx.strategySearchProgress(strategy) : null;
        return FixStrategyAttemptDto.builder()
                .strategy(strategy)
                .status(status)
                .reason(reason)
                .attemptsUsed(progress != null ? progress.attemptsUsed() : null)
                .attemptLimit(progress != null ? progress.attemptLimit() : null)
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
        log.warn("Could not resolve violatedSpecId '{}' to spec index", violatedSpecId);
        return -1;
    }
}
