package cn.edu.nju.Iot_Verify.dto.model;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * Per-value semantic provenance for one environment variable in a frozen verification/simulation run.
 *
 * <p>This makes historical counterexamples self-explanatory: every transition can be attributed to
 * either a user declaration or a disclosed abstraction, without consulting the current Board.
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class EnvironmentValueProvenanceDto {

    public enum ValueType {
        NUMERIC,
        DISCRETE_ENUM,
        DISCRETE_BOOLEAN
    }

    /**
     * Authorship category determines evolution semantics.
     *
     * <ul>
     * <li>EXOGENOUS: no device declares ImpactedVariables; may take any declared value each step
     *     (deliberate abstraction for discrete, exact for numeric with natural rate).</li>
     * <li>DEVICE_CONTROLLED: at least one device declares ImpactedVariables; stutters when no
     *     declared effect applies (exact semantics).</li>
     * <li>COMPOSED: several devices declare ImpactedVariables. Numeric effects sum, which is
     *     MEDIC's additive {@code env.D.v}. Discrete writers must agree: a scene whose declared
     *     effects assign different values to one discrete value is rejected at board assembly,
     *     because resolving it by iteration order made the same scene produce opposite verdicts.
     *     So a COMPOSED discrete value here is one whose writers agree (exact semantics).</li>
     * </ul>
     */
    public enum AuthorshipCategory {
        EXOGENOUS,
        DEVICE_CONTROLLED,
        COMPOSED
    }

    /**
     * Whether the evolution rule is exact (means what the user declared) or a conservative
     * over-approximation (disclosed abstraction).
     */
    public enum SemanticsTag {
        /** Means what the user declared, or what the device template explicitly states. */
        EXACT,
        /** Deliberate conservative over-approximation disclosed in modelSemantics. */
        ABSTRACTION
    }

    /**
     * One device that declares ImpactedVariables for this environment value.
     */
    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    public static class DeviceWriter {
        /** NuSMV variable name for this device instance. */
        private String deviceVarName;

        /** Template display name. */
        private String templateName;

        /** Whether the template is bundled, custom, or unknown. */
        private ModelTokenSource templateSource;
    }

    /**
     * One device that declares Reads=true for this environment value.
     */
    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    public static class DeviceReader {
        /** NuSMV variable name for this device instance. */
        private String deviceVarName;
    }

    /** User-facing environment variable name. */
    private String name;

    private ValueType type;

    /** For numeric: lower bound of the declared domain. */
    private Integer lowerBound;

    /** For numeric: upper bound of the declared domain. */
    private Integer upperBound;

    /** For numeric: natural evolution rate (e.g., "increase" / "decrease" / "stable"). */
    private String naturalChangeRate;

    /** For discrete: the declared values (enum or boolean). */
    private List<String> values;

    private AuthorshipCategory authorship;

    /** Devices that declare ImpactedVariables for this value. Empty for purely exogenous. */
    private List<DeviceWriter> writers;

    /** Devices that declare Reads=true for this value. */
    private List<DeviceReader> readers;

    /** EXACT when user-declared; ABSTRACTION for purely exogenous discrete. */
    private SemanticsTag semantics;

    /**
     * Human-readable summary of the evolution rule for user-facing disclosure.
     * Example: "External input (weather); may change to any declared value each step (deliberate abstraction)."
     */
    private String evolutionSummary;
}
