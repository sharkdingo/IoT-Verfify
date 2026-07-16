package cn.edu.nju.Iot_Verify.component.fuzz;

import java.util.List;

/** Stable codes shared by paper-compatible execution and its read-only domain preview. */
public final class FuzzPaperSemantics {

    public static final String INITIALIZATION_POLICY = "RANDOM_LEGAL_PER_SEED";
    public static final String CHANGE_RATE = "CHANGE_RATE";
    public static final String DIRECT_VALUE_EXTENSION = "DIRECT_VALUE_EXTENSION";

    private static final List<String> LIMITATION_CODES = List.of(
            "PAPER_EVENT_FSM_DISTANCE_ENABLED",
            "PAPER_RANDOM_INITIAL_STATE_ENABLED",
            "PAPER_STRUCTURED_LTL_TEMPLATES_ONLY",
            "PAPER_INTEGER_NUMERIC_DOMAIN_ONLY",
            "PAPER_DISCRETE_ENVIRONMENT_DIRECT_VALUE_EXTENSION",
            "PAPER_PREDECESSOR_STATE_OUTPUTS_THREE_LEVELS_ONLY",
            "PAPER_MULTI_TARGET_PRODUCT_EXTENSION",
            "NUSMV_REMAINS_PROOF_AUTHORITY"
    );

    private FuzzPaperSemantics() {
    }

    public static List<String> limitationCodes() {
        return LIMITATION_CODES;
    }
}
