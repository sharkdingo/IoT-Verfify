package cn.edu.nju.Iot_Verify.dto.trace;

import com.fasterxml.jackson.annotation.JsonInclude;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * Trace state in one counterexample step.
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class TraceStateDto {
    @NotNull(message = "State index is required")
    private Integer stateIndex;

    @Valid
    @NotNull(message = "Devices list is required")
    private List<TraceDeviceDto> devices;

    /** Rules whose modeled transition branch produced this state. Empty means none fired. */
    @Valid
    @NotNull(message = "Triggered rules list is required")
    private List<TraceTriggeredRuleDto> triggeredRules;

    /** Automation delivery links selected as compromised in this model branch. */
    @Valid
    @NotNull(message = "Compromised automation links list is required")
    private List<TraceTriggeredRuleDto> compromisedAutomationLinks;

    @Valid
    private List<TraceTrustPrivacyDto> trustPrivacies;

    /**
     * Board-level environment variables in this state, using user-facing environment names, e.g. temperature.
     */
    @Valid
    private List<TraceVariableDto> envVariables;

    /**
     * Model runtime values that are not part of the user's environment pool, such as
     * the user-facing {@code compromisedPointCount}. Internal NuSMV names are translated by the parser.
     */
    @Valid
    private List<TraceVariableDto> globalVariables;

    /**
     * This state begins the repeating cycle of an infinite counterexample path.
     *
     * <p>A liveness property (templates 2, 5 and 6 — {@code AF}, {@code AG(IF -> AF THEN)} and the
     * {@code LTLSPEC} persistence form, whose negations are {@code EG}/{@code GF}) is refuted by a lasso
     * path, not by a finite prefix: NuSMV prints {@code -- Loop starts here} and the violation *is* the
     * cycle that never reaches the required state. Absent for finite traces, which is every simulation and
     * fuzz trace and most formal ones.
     *
     * <p>Template 2 belongs in that set and was omitted here: measured on NuSMV 2.7.1, an {@code AF(A)}
     * refutation prints the marker before State 1.1, so the whole trace is the cycle. Every other site
     * naming this set — {@code spec-templates.md}, {@code types/verify.ts}, {@code Board.vue}'s
     * {@code LIVENESS_TEMPLATES} — lists 2, 5 and 6.
     */
    private Boolean loopStart;

    /**
     * This state closes the cycle by repeating the {@link #loopStart} state.
     *
     * <p>NuSMV re-prints the loop entry as a final state, so the merged state always equals the
     * {@link #loopStart} state — but whether it equals its own *predecessor* depends on the cycle length,
     * measured on NuSMV 2.7.1:
     *
     * <ul>
     *   <li>A one-state cycle prints the closing state with no variable lines, so the delta merge
     *       reproduces the predecessor exactly and playback shows a step where nothing moves.</li>
     *   <li>A longer cycle prints the deltas needed to get back to the entry, so the closing state
     *       differs from its predecessor and playback shows an ordinary-looking step.</li>
     * </ul>
     *
     * <p>Both cases need the flag, for opposite reasons: the first is indistinguishable from a stalled run,
     * and the second is indistinguishable from the path continuing. Neither can be inferred from the values
     * without comparing against the loop entry, which a paginated state window need not contain.
     */
    private Boolean loopBack;
}
