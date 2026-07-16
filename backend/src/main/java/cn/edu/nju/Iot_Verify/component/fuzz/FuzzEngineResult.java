package cn.edu.nju.Iot_Verify.component.fuzz;

import java.util.List;

public record FuzzEngineResult(
        FuzzEngineOutcome outcome,
        long effectiveSeed,
        int iterations,
        long generatedPaths,
        long elapsedMs,
        List<FuzzFinding> findings,
        List<FuzzSpecEligibility> eligibility,
        List<String> limitations) {

    public FuzzEngineResult {
        findings = findings == null ? List.of() : List.copyOf(findings);
        eligibility = eligibility == null ? List.of() : List.copyOf(eligibility);
        limitations = limitations == null ? List.of() : List.copyOf(limitations);
    }
}
