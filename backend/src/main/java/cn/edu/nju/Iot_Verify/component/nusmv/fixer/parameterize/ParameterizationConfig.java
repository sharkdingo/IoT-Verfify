package cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Describes parameterization modifications to a standard SMV model,
 * used by both §5.1 (Parameter Adjustment) and §5.2 (Condition Adjustment).
 *
 * <p>FROZENVAR variables are non-deterministically chosen at init and never change,
 * allowing NuSMV to "solve" for values that satisfy or violate a spec.</p>
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class ParameterizationConfig {

    /**
     * §5.1: Numeric threshold parameterization.
     * Key = "r{ruleIdx}_c{condIdx}", value = parameter metadata.
     */
    @Builder.Default
    private Map<String, ParamInfo> parameterizedThresholds = new LinkedHashMap<>();

    /**
     * §5.2: Condition lambda guards.
     * Key = "r{ruleIdx}_c{condIdx}", value = FROZENVAR name (e.g. "lambda_r0_c1").
     */
    @Builder.Default
    private Map<String, String> conditionLambdas = new LinkedHashMap<>();

    /**
     * Index of the violated spec in the specs list; this spec will be negated (¬ρ).
     */
    private int negatedSpecIndex;

    /**
     * INVAR clauses to exclude previously-tried parameter configurations (§5.1 iteration).
     */
    @Builder.Default
    private List<String> exclusionInvars = new ArrayList<>();

    /**
     * Metadata for a parameterized numeric threshold (§5.1).
     */
    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    public static class ParamInfo {
        /** FROZENVAR name, e.g. "param_r0_c1" */
        private String frozenVarName;
        private int lowerBound;
        private int upperBound;
        /** Original threshold value in the rule condition */
        private String originalValue;
    }
}
