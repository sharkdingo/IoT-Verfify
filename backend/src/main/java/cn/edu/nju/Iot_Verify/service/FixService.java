package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.fix.FaultLocalizationResultDto;
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
    FaultLocalizationResultDto localizeFault(Long userId, Long traceId);

    /**
     * Attempt to fix a violation with optional preferred parameter ranges keyed by ParameterAdjustment.targetId
     * (may invoke NuSMV multiple times).
     */
    FixResultDto fix(Long userId, Long traceId, List<String> strategies, Map<String, PreferredRange> preferredRanges);

    /**
     * Apply a repair strategy to the user's persisted board rules.
     *
     * <p>The caller supplies the exact displayed suggestion and its server-issued signature. The
     * service checks the signature and board/template drift before persisting that same change.</p>
     */
    FixApplyResultDto applyFix(Long userId, Long traceId, String strategy,
                               FixSuggestionDto suggestion, String suggestionToken,
                               Map<String, PreferredRange> preferredRanges);

    /**
     * Internal compatibility overload for service-level callers that need to assert a submitted
     * suggestion against the server recomputation. It is not exposed by the REST API.
     */
    @Deprecated
    FixApplyResultDto applyFix(Long userId, Long traceId, String strategy, FixSuggestionDto suggestion,
                               Map<String, PreferredRange> preferredRanges);
}
