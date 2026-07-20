package cn.edu.nju.Iot_Verify.component.nusmv.fixer;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.ParameterTarget;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import lombok.Builder;
import lombok.Getter;

import java.time.Instant;
import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Immutable context passed to all {@link FixStrategy} implementations,
 * consolidating the parameters needed for fix attempts.
 */
@Getter
@Builder
public class FixContext {
    private final Long traceId;
    private final List<FaultRuleDto> faultRules;
    private final List<RuleDto> allRules;
    private final List<DeviceVerificationDto> devices;
    @Builder.Default
    private final List<BoardEnvironmentVariableDto> environmentVariables = List.of();
    private final List<SpecificationDto> specs;
    private final Map<String, DeviceSmvData> deviceSmvMap;
    private final int violatedSpecIndex;
    private final Long userId;
    private final boolean isAttack;
    private final int attackBudget;
    private final AttackScenarioDto attackScenario;
    private final boolean enablePrivacy;
    private final int maxAttempts;
    private final Map<String, PreferredRange> preferredRanges;
    /** First complete state of the persisted counterexample used only for candidate solving. */
    private final TraceStateDto counterexampleInitialState;
    /** Production fixer paths require replay; low-level strategy tests may omit it explicitly. */
    private final boolean requireCounterexampleReplay;
    private final Instant deadline;

    @Builder.Default
    private final Set<String> diagnostics = new LinkedHashSet<>();
    @Builder.Default
    private final Map<String, String> strategyGenerationFailures = new LinkedHashMap<>();
    @Builder.Default
    private final Map<String, String> strategySolverFailures = new LinkedHashMap<>();
    @Builder.Default
    private final Map<String, StrategyNoResult> strategyNoResults = new LinkedHashMap<>();
    @Builder.Default
    private final Map<String, StrategySearchProgress> strategySearchProgress = new LinkedHashMap<>();
    @Builder.Default
    private final Map<String, ParameterTarget> parameterTargets = new LinkedHashMap<>();
    @Builder.Default
    private final Set<String> matchedPreferredRangeTargetIds = new LinkedHashSet<>();

    /**
     * Returns true if the fix deadline has passed.
     * Returns false if no deadline was set (null = no timeout).
     */
    public boolean isExpired() {
        return deadline != null && Instant.now().isAfter(deadline);
    }

    /** Remaining wall-clock budget for a child NuSMV call, in whole milliseconds. */
    public long remainingMillis() {
        if (deadline == null) {
            return Long.MAX_VALUE;
        }
        return Math.max(0, Duration.between(Instant.now(), deadline).toMillis());
    }

    public synchronized void addDiagnostic(String diagnostic) {
        if (diagnostic != null && !diagnostic.isBlank()) {
            diagnostics.add(diagnostic);
        }
    }

    public synchronized List<String> diagnosticsSnapshot() {
        return new ArrayList<>(diagnostics);
    }

    public synchronized void clearStrategyGenerationFailure(String strategy) {
        strategyGenerationFailures.remove(strategy);
    }

    public synchronized void recordStrategyGenerationFailure(String strategy, String reason) {
        if (strategy != null && !strategy.isBlank() && reason != null && !reason.isBlank()) {
            strategyGenerationFailures.put(strategy, reason);
        }
    }

    public synchronized String strategyGenerationFailure(String strategy) {
        return strategyGenerationFailures.get(strategy);
    }

    public synchronized void clearStrategySolverFailure(String strategy) {
        strategySolverFailures.remove(strategy);
    }

    public synchronized void recordStrategySolverFailure(String strategy, String reason) {
        if (strategy != null && !strategy.isBlank() && reason != null && !reason.isBlank()) {
            strategySolverFailures.put(strategy, reason);
        }
    }

    public synchronized String strategySolverFailure(String strategy) {
        return strategySolverFailures.get(strategy);
    }

    public synchronized void clearStrategyNoResult(String strategy) {
        strategyNoResults.remove(strategy);
    }

    public synchronized void recordStrategyNoResult(String strategy, String status, String reason) {
        if (strategy != null && !strategy.isBlank() && status != null && !status.isBlank()
                && reason != null && !reason.isBlank()) {
            strategyNoResults.put(strategy, new StrategyNoResult(status, reason));
        }
    }

    public synchronized StrategyNoResult strategyNoResult(String strategy) {
        return strategyNoResults.get(strategy);
    }

    public synchronized void initializeStrategySearch(String strategy, int attemptLimit) {
        if (strategy != null && !strategy.isBlank()) {
            strategySearchProgress.put(strategy,
                    new StrategySearchProgress(0, Math.max(0, attemptLimit)));
        }
    }

    public synchronized void addStrategyAttempts(String strategy, int attempts) {
        if (strategy == null || strategy.isBlank() || attempts <= 0) {
            return;
        }
        StrategySearchProgress current = strategySearchProgress.get(strategy);
        if (current == null) {
            strategySearchProgress.put(strategy, new StrategySearchProgress(attempts, attempts));
            return;
        }
        long updated = (long) current.attemptsUsed() + attempts;
        strategySearchProgress.put(strategy, new StrategySearchProgress(
                (int) Math.min(updated, current.attemptLimit()), current.attemptLimit()));
    }

    public synchronized StrategySearchProgress strategySearchProgress(String strategy) {
        return strategySearchProgress.get(strategy);
    }

    public synchronized void registerParameterTarget(ParameterTarget target) {
        if (target != null && target.getTargetId() != null && !target.getTargetId().isBlank()) {
            parameterTargets.putIfAbsent(target.getTargetId(), target);
        }
    }

    public synchronized List<ParameterTarget> parameterTargetsSnapshot() {
        return new ArrayList<>(parameterTargets.values());
    }

    public synchronized void markPreferredRangeTargetMatched(String targetId) {
        if (targetId != null && !targetId.isBlank()) {
            matchedPreferredRangeTargetIds.add(targetId);
        }
    }

    public synchronized Set<String> matchedPreferredRangeTargetIdsSnapshot() {
        return new LinkedHashSet<>(matchedPreferredRangeTargetIds);
    }

    public AttackScenarioDto resolvedAttackScenario() {
        if (attackScenario != null) {
            return attackScenario;
        }
        return isAttack ? AttackScenarioDto.anyUpToBudget(attackBudget) : AttackScenarioDto.none();
    }

    public record StrategyNoResult(String status, String reason) {
    }

    public record StrategySearchProgress(int attemptsUsed, int attemptLimit) {
    }
}
