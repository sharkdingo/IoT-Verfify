package cn.edu.nju.Iot_Verify.component.nusmv.fixer;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import lombok.Builder;
import lombok.Getter;

import java.time.Instant;
import java.time.Duration;
import java.util.ArrayList;
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
    private final Instant deadline;

    @Builder.Default
    private final Set<String> diagnostics = new LinkedHashSet<>();

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

    public AttackScenarioDto resolvedAttackScenario() {
        if (attackScenario != null) {
            return attackScenario;
        }
        return isAttack ? AttackScenarioDto.anyUpToBudget(attackBudget) : AttackScenarioDto.none();
    }
}
