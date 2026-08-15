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
     * <p>A liveness property (templates 5 and 6, whose negations are {@code EG}/{@code GF}) is refuted by a
     * lasso path, not by a finite prefix: NuSMV prints {@code -- Loop starts here} and the violation *is* the
     * cycle that never reaches the required state. Absent for finite traces, which is every simulation and
     * fuzz trace and most formal ones.
     */
    private Boolean loopStart;

    /**
     * This state closes the cycle by repeating the {@link #loopStart} state.
     *
     * <p>NuSMV re-prints the loop entry as a final state carrying no variable lines, which the delta merge
     * materializes into a full state identical to its predecessor. Without this flag it plays back as an
     * ordinary step in which nothing changes, hiding the one fact the state exists to convey.
     */
    private Boolean loopBack;
}
