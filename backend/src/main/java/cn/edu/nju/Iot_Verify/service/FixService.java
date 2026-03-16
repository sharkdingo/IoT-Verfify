package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;

import java.util.List;
import java.util.Map;

public interface FixService {

    /**
     * Localize fault rules from a counterexample trace (fast, pure in-memory).
     */
    List<FaultRuleDto> localizeFault(Long userId, Long traceId);

    /**
     * Attempt to fix a violation with optional preferred parameter ranges (may invoke NuSMV multiple times).
     */
    FixResultDto fix(Long userId, Long traceId, List<String> strategies, Map<String, PreferredRange> preferredRanges);
}
