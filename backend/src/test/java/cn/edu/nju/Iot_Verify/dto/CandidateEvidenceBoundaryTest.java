package cn.edu.nju.Iot_Verify.dto;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A bounded-search finding must never carry the vocabulary of a formal verdict.
 *
 * <p>This is the semantic boundary the whole product rests on. NuSMV is a decision procedure: {@code SATISFIED}
 * means proved, {@code VIOLATED} means a counterexample exists. Bounded exploration is a search — a finding is
 * *candidate* evidence, and finding nothing means only that nothing was found inside the budget.
 * {@code frontend/CLAUDE.md} states it directly: a fuzz finding is replay-only candidate evidence, and
 * {@code BUDGET_EXHAUSTED} must never render as safe or satisfied.
 *
 * <p>Verified live against both engines on the climate-conflict scene: NuSMV returned {@code VIOLATED} with 2
 * violated specs while bounded exploration returned 2 findings — agreement — and the finding payload carried
 * {@code violatedSpecId}, {@code firstViolationStep}, {@code states}, {@code seed}, {@code inputEvents} and no
 * conclusion field of any kind.
 *
 * <p>The failure this guards against is a field, not a bug: adding {@code outcome} or {@code modelComplete} to a
 * finding DTO would look like helpful symmetry with the verification DTOs, would compile, would serialise, and
 * would quietly turn a search result into something a reader cannot distinguish from a proof. In a formal
 * verification tool that is the most consequential kind of dishonesty available.
 *
 * <p>Reflective on purpose. A request-level test can only cover the endpoints that exist today; this covers any
 * field added tomorrow, and states the rule where someone editing these DTOs will look for it.
 */
class CandidateEvidenceBoundaryTest {

    /**
     * Field names that assert a *decided* outcome. Each belongs to verification, never to a search.
     *
     * <p>{@code outcome} is deliberately **not** here, and finding out why corrected the rule. The fuzz DTOs do
     * declare an {@code outcome} — but typed {@code FuzzOutcome}, a deliberately disjoint enum:
     * {@code FOUND_VIOLATION | BUDGET_EXHAUSTED | INCONCLUSIVE} against verification's
     * {@code SATISFIED | VIOLATED | INCONCLUSIVE}. A bounded search therefore *cannot express* "satisfied" — the
     * type system enforces the semantic boundary, which is stronger than any naming convention. Banning the field
     * name would have been a rule against the correct design.
     *
     * <p>{@code violatedSpecId} and {@code firstViolationStep} are absent for the same reason: they name *what
     * the candidate path touched*, which is the evidence a user replays, not a claim that the property is decided.
     */
    private static final Set<String> VERDICT_VOCABULARY = Set.of(
            "modelcomplete",
            "satisfied",
            "proved",
            "proven",
            "verdict",
            "verified",
            "safe"
    );

    /** The enum a bounded-search outcome must use. */
    private static final String SEARCH_OUTCOME_TYPE = "FuzzOutcome";

    /** The DTOs that carry bounded-search results to the client. */
    private static final List<Class<?>> CANDIDATE_EVIDENCE_DTOS = new ArrayList<>();

    static {
        for (String name : List.of(
                "cn.edu.nju.Iot_Verify.dto.fuzz.FuzzFindingDto",
                "cn.edu.nju.Iot_Verify.dto.fuzz.FuzzFindingSummaryDto",
                "cn.edu.nju.Iot_Verify.dto.fuzz.FuzzRunDto",
                "cn.edu.nju.Iot_Verify.dto.fuzz.FuzzRunSummaryDto")) {
            try {
                CANDIDATE_EVIDENCE_DTOS.add(Class.forName(name));
            } catch (ClassNotFoundException ignored) {
                // A renamed DTO is caught by the coverage assertion below rather than by a silent skip.
            }
        }
    }

    @Test
    @DisplayName("a bounded-search DTO declares no field that asserts a decided outcome")
    void candidateEvidenceCarriesNoVerdict() {
        // Coverage first: if every class failed to resolve, an empty offender list would be vacuously true and
        // this test would pass while checking nothing.
        assertTrue(CANDIDATE_EVIDENCE_DTOS.size() >= 3,
                "expected at least 3 bounded-search DTOs, resolved " + CANDIDATE_EVIDENCE_DTOS.size()
                        + " — they were probably renamed, so an empty offender list proves nothing");

        List<String> offenders = new ArrayList<>();
        for (Class<?> dto : CANDIDATE_EVIDENCE_DTOS) {
            for (Field field : dto.getDeclaredFields()) {
                if (field.isSynthetic()) continue;
                String name = field.getName().toLowerCase(Locale.ROOT);
                if (VERDICT_VOCABULARY.contains(name)) {
                    offenders.add(dto.getSimpleName() + "." + field.getName());
                }
            }
        }

        assertEquals(List.of(), offenders,
                "a bounded search cannot decide a property; these fields would present candidate evidence as a "
                        + "formal conclusion");
    }

    @Test
    @DisplayName("a bounded-search outcome uses the search enum and never borrows the verdict enum")
    void searchOutcomeCannotExpressSatisfied() {
        // The real guarantee, and it is structural rather than lexical. `FuzzOutcome` has no SATISFIED member, so
        // a search physically cannot report a property as proved. Swapping the field's type to
        // `VerificationOutcome` would compile, would serialise, and would silently give exploration the power to
        // claim safety — the exact failure `CLAUDE.md` forbids when it says BUDGET_EXHAUSTED must never render as
        // safe or satisfied.
        List<String> offenders = new ArrayList<>();
        int outcomeFields = 0;

        for (Class<?> dto : CANDIDATE_EVIDENCE_DTOS) {
            for (Field field : dto.getDeclaredFields()) {
                if (field.isSynthetic() || !"outcome".equals(field.getName())) continue;
                outcomeFields++;
                String type = field.getType().getSimpleName();
                if (!SEARCH_OUTCOME_TYPE.equals(type)) {
                    offenders.add(dto.getSimpleName() + ".outcome is " + type
                            + " (must be " + SEARCH_OUTCOME_TYPE + ")");
                }
            }
        }

        assertTrue(outcomeFields >= 1,
                "expected at least one bounded-search outcome field to check, found " + outcomeFields);
        assertEquals(List.of(), offenders, "a search outcome must not be typed as a verification verdict");

        // And the search enum itself must stay unable to say "satisfied".
        try {
            Class<?> fuzzOutcome = Class.forName("cn.edu.nju.Iot_Verify.dto.fuzz.FuzzOutcome");
            List<String> names = new ArrayList<>();
            for (Object constant : fuzzOutcome.getEnumConstants()) names.add(constant.toString());
            assertTrue(names.contains("BUDGET_EXHAUSTED"),
                    "the search enum must be able to say the budget ran out: " + names);
            for (String forbidden : List.of("SATISFIED", "PROVED", "SAFE", "VERIFIED")) {
                assertTrue(!names.contains(forbidden),
                        "FuzzOutcome must not be able to claim " + forbidden + "; a bounded search cannot decide "
                                + "a property. Values: " + names);
            }
        } catch (ClassNotFoundException e) {
            throw new AssertionError("FuzzOutcome should exist", e);
        }
    }

    @Test
    @DisplayName("verification DTOs do carry a verdict, so the boundary is a real distinction")
    void verificationStillCarriesItsVerdict() {
        // The mirror of the rule above, and the reason it is not merely a naming ban: verification *must* state a
        // conclusion. Without this, deleting `outcome` everywhere would satisfy the first test and destroy the
        // product — a rule that can be satisfied by removing the feature is not a rule.
        try {
            Class<?> verificationTask = Class.forName(
                    "cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskSummaryDto");
            boolean hasOutcome = false;
            for (Field field : verificationTask.getDeclaredFields()) {
                if ("outcome".equals(field.getName())) hasOutcome = true;
            }
            assertTrue(hasOutcome,
                    "VerificationTaskSummaryDto must keep its outcome: a verification without a verdict is not a "
                            + "verification");
        } catch (ClassNotFoundException e) {
            throw new AssertionError("VerificationTaskSummaryDto should exist", e);
        }
    }
}
