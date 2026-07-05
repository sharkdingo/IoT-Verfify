package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixApplyResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
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

    /**
     * Apply a fix suggestion to the user's persisted board rules and save.
     *
     * <p>The server re-derives the fix (NuSMV-verified) for the given strategy and requires the submitted
     * suggestion to match it, so the client's {@code verified} flag is not trusted. {@code preferredRanges}
     * must be the same ranges /fix used to produce the suggestion, so the recompute reproduces it.</p>
     *
     * <p>The suggestion's rule/condition indices are computed against the trace's verification-time
     * rule snapshot. This method aligns the snapshot with the current board rules (index + fingerprint)
     * and rejects the apply if the board drifted, to avoid editing the wrong rule.</p>
     */
    FixApplyResultDto applyFix(Long userId, Long traceId, String strategy, FixSuggestionDto suggestion,
                               Map<String, PreferredRange> preferredRanges);
}
