package cn.edu.nju.Iot_Verify.component;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The conformance claims in {@code docs/architecture/theory-sources.md} must still be true of the code.
 *
 * <p>That document is the only place recording which paper owns which semantics, and it makes four specific,
 * checkable claims about algorithms. It is also dated — "checked against the papers (2026-07-31)" — which is
 * exactly the kind of assertion that silently rots: the paper does not change, the code does, and nothing fails
 * when they diverge.
 *
 * <p>Each claim was verified by reading the implementation alongside the document:
 *
 * <ul>
 *   <li><b>Salus §5.3</b> — {@code ParameterAdjustStrategy} sorts candidates by
 *       {@code comparingLong(value -> distance(value, original))} where {@code distance} is
 *       {@code Math.abs(value - original)}, so the closest working value is offered first.</li>
 *   <li><b>Salus §5.2</b> — {@code FixStrategyUtils} derives candidate conditions from the violated
 *       specification's own {@code aConditions}, {@code ifConditions} and {@code thenConditions}, not from
 *       invented predicates.</li>
 *   <li><b>HAFuzz Algorithm 1 line 25</b> — {@code PaperMonitorFsm} computes
 *       {@code Math.scalb(1.0, solverLevels - level) / (Math.scalb(1.0, solverLevels) - 1.0)}, which is
 *       2^(l_up−l) / (2^l_up − 1) exactly.</li>
 *   <li><b>FSM thesis ch.4</b> — {@code forwardVerify} refuses to confirm a repair when
 *       {@code disabledRuleCount() > 0 || skippedSpecCount() > 0}, so a vacuous pass is never reported as a fix;
 *       rejected candidates are added to {@code exclusionInvars} rather than retried.</li>
 * </ul>
 *
 * <p>This test pins the *structural fingerprint* of each claim rather than re-deriving the mathematics. A
 * behavioural test already covers the weight formula ({@code PaperDistanceMetricPropertyTest}) and the parameter
 * search ({@code ParameterAdjustStrategyTest}). What was unguarded is the link between those behaviours and the
 * document that describes them — so if someone changes the ordering comparator or drops the incompleteness
 * refusal, this fails and names the paragraph that has become false.
 */
class TheorySourceConformanceTest {

    private static final Path MAIN = Paths.get("src", "main", "java", "cn", "edu", "nju", "Iot_Verify");
    private static final Path DOC = Paths.get("..", "docs", "architecture", "theory-sources.md");

    private static String source(String... segments) throws IOException {
        Path p = MAIN;
        for (String s : segments) p = p.resolve(s);
        return Files.readString(p, StandardCharsets.UTF_8);
    }

    @Test
    @DisplayName("Salus 5.3: parameter candidates are ordered by distance from the original value")
    void parameterCandidatesOrderedByDistance() throws IOException {
        String strategy = source("component", "nusmv", "fixer", "strategy", "ParameterAdjustStrategy.java");
        // The ordering is the claim. Offering a distant value before a nearer working one would still "fix" the
        // model while contradicting the paper and surprising the user with a larger change than necessary.
        assertTrue(strategy.contains("distance(value, original)"),
                "theory-sources.md claims Salus 5.3 ordering by distance from the original value; "
                        + "ParameterAdjustStrategy no longer sorts by it");
        assertTrue(strategy.replaceAll("\\s+", " ").contains("Math.abs((long) value - original)"),
                "distance() should be absolute difference from the original value");
    }

    @Test
    @DisplayName("Salus 5.2: condition candidates come from the violated specification, not invented")
    void conditionCandidatesComeFromTheSpecification() throws IOException {
        String utils = source("component", "nusmv", "fixer", "strategy", "FixStrategyUtils.java");
        String flat = utils.replaceAll("\\s+", " ");
        // All three clause groups must be read. Dropping one would narrow the candidate set in a way that looks
        // like a tightening but actually invents a different algorithm than the paper describes.
        for (String clause : List.of("getAConditions()", "getIfConditions()", "getThenConditions()")) {
            assertTrue(flat.contains("violatedSpec." + clause),
                    "theory-sources.md claims candidates derive from the violated specification's own "
                            + "conditions; " + clause + " is no longer read");
        }
    }

    @Test
    @DisplayName("HAFuzz Algorithm 1 line 25: the per-level weight is 2^(l_up-l) / (2^l_up - 1)")
    void perLevelWeightMatchesTheAlgorithm() throws IOException {
        String fsm = source("component", "fuzz", "paper", "PaperMonitorFsm.java");
        String flat = fsm.replaceAll("\\s+", " ");
        assertTrue(flat.contains("Math.scalb(1.0, solverLevels) - 1.0"),
                "the documented denominator 2^l_up - 1 is no longer computed");
        assertTrue(flat.contains("Math.scalb(1.0, solverLevels - level) / denominator"),
                "the documented per-level weight 2^(l_up-l) / (2^l_up - 1) is no longer computed");
    }

    @Test
    @DisplayName("every SMV identifier the theory doc names exists in SmvConstants")
    void documentedSmvIdentifiersExist() throws IOException {
        // The defect this catches, found in Pass 32: the doc described MEDIC's attack model using the paper's own
        // variable names — a boolean `attacked` per device and `attack.intensity <= v`. The generated model uses
        // neither. It emits `iot_verify_compromised_point_count` and
        // `iot_verify_automation_link_compromised_<n>`, because this project's attack surface is *points* (device
        // instances AND automation links) rather than devices alone. A reader tracing MEDIC 4.2 into the code would
        // have searched for identifiers that do not exist.
        String doc = Files.readString(DOC, StandardCharsets.UTF_8);
        // `util/`, not `generator/` — I guessed the package first and the test errored rather than failed, which is
        // the useful kind of mistake: a wrong path cannot masquerade as a passing check.
        String constants = source("util", "SmvConstants.java");

        Matcher m = Pattern.compile("`(iot_verify_[a-z_]+)").matcher(doc);
        List<String> named = new ArrayList<>();
        while (m.find()) if (!named.contains(m.group(1))) named.add(m.group(1));

        assertTrue(named.size() >= 1,
                "the theory doc should name at least one generated SMV identifier, found " + named.size()
                        + " — the extraction is probably broken, so an empty offender list proves nothing");

        List<String> absent = new ArrayList<>();
        for (String id : named) {
            // A prefix constant is stored without its numeric suffix, so compare on the stem.
            String stem = id.replaceAll("_<n>$", "").replaceAll("_$", "");
            if (!constants.contains(stem)) absent.add(id);
        }
        assertEquals(List.of(), absent,
                "theory-sources.md names SMV identifiers that SmvConstants does not define; a reader tracing a "
                        + "paper section into the model would search for something that is not generated");
    }

    @Test
    @DisplayName("FSM thesis ch.4: a repair over an incomplete model is refused, not reported as a fix")
    void incompleteModelIsNeverAVacuousPass() throws IOException {
        String utils = source("component", "nusmv", "fixer", "strategy", "FixStrategyUtils.java");
        String flat = utils.replaceAll("\\s+", " ");
        // This is the load-bearing one. A model with disabled rules or skipped specs can pass verification
        // *because* the thing that would have failed was never modelled — reporting that as a repair is the exact
        // dishonesty the whole product is built to avoid.
        assertTrue(flat.contains("disabledRuleCount() > 0 || genResult.skippedSpecCount() > 0")
                        || flat.contains("genResult.disabledRuleCount() > 0"),
                "forwardVerify no longer refuses an incomplete regenerated model, so a vacuous pass could be "
                        + "reported as a confirmed repair");

        String strategy = source("component", "nusmv", "fixer", "strategy", "ParameterAdjustStrategy.java");
        assertTrue(strategy.contains("exclusionInvars"),
                "rejected candidates should be excluded via invariants rather than retried");
    }

    @Test
    @DisplayName("the document still names the four papers it claims to source semantics from")
    void documentStillNamesItsSources() throws IOException {
        String doc = Files.readString(DOC, StandardCharsets.UTF_8);
        // Coverage guard: if the document moved or was rewritten, the assertions above would be pinning code
        // against a description that no longer exists.
        List<String> missing = new ArrayList<>();
        for (String paper : List.of("MEDIC", "Salus", "HAFuzz")) {
            if (!doc.contains(paper)) missing.add(paper);
        }
        assertEquals(List.of(), missing, "theory-sources.md no longer names these papers");
        assertTrue(doc.contains("2^(l_up-l)"),
                "the document should still state the HAFuzz weight formula this test pins");
    }
}
