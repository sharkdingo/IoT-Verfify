package cn.edu.nju.Iot_Verify.component.nusmv.fixer;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import lombok.Builder;
import lombok.Getter;

import java.time.Instant;
import java.util.List;
import java.util.Map;

/**
 * Immutable context passed to all {@link FixStrategy} implementations,
 * consolidating the parameters needed for fix attempts.
 */
@Getter
@Builder
public class FixContext {
    private final List<FaultRuleDto> faultRules;
    private final List<RuleDto> allRules;
    private final List<DeviceVerificationDto> devices;
    private final List<SpecificationDto> specs;
    private final Map<String, DeviceSmvData> deviceSmvMap;
    private final int violatedSpecIndex;
    private final Long userId;
    private final boolean isAttack;
    private final int intensity;
    private final boolean enablePrivacy;
    private final int maxAttempts;
    private final Map<String, PreferredRange> preferredRanges;
    private final Instant deadline;

    /**
     * Returns true if the fix deadline has passed.
     * Returns false if no deadline was set (null = no timeout).
     */
    public boolean isExpired() {
        return deadline != null && Instant.now().isAfter(deadline);
    }
}
