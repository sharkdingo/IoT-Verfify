package cn.edu.nju.Iot_Verify.dto.fuzz;

/** A bounded fuzz run never proves that a specification is satisfied. */
public enum FuzzOutcome {
    FOUND_VIOLATION,
    BUDGET_EXHAUSTED,
    INCONCLUSIVE
}
