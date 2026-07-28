package cn.edu.nju.Iot_Verify.component.ai.chat;

import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The reasoning channel is the only one carrying an argument rather than a status, so it has its own
 * presentation contract: keep the structure, keep the prose, cut on a boundary.
 */
class ChatToolProgressPresenterReasoningTest {

    private final ChatToolProgressPresenter presenter =
            new ChatToolProgressPresenter(new ObjectMapper());

    @Test
    void reasoningKeepsTheLineStructureTheModelProduced() {
        String reasoning = """
                Goal: decide whether the bedroom can overheat.
                Observed: the heater rule has no upper bound.
                Next: verify the temperature ceiling.""";

        String presented = presenter.compactReasoningProgressDetail(reasoning);

        assertEquals(3, presented.split("\n").length,
                "collapsing newlines turned a decomposition into one run-on line");
        assertTrue(presented.contains("Goal: decide"));
        assertTrue(presented.contains("Next: verify"));
    }

    @Test
    void ordinaryHyphenatedEnglishIsNotRedactedAsAnIdentifier() {
        String presented = presenter.compactReasoningProgressDetail(
                "A rule-based check at device-level is trace-driven, so simulation-only "
                        + "evidence is weaker.");

        assertFalse(presented.contains("[internal reference]"),
                "the redaction corrupted the explanation it was meant to protect");
        assertTrue(presented.contains("rule-based"));
        assertTrue(presented.contains("device-level"));
    }

    @Test
    void generatedIdentifiersAndTokensAreStillRemoved() {
        String presented = presenter.compactReasoningProgressDetail(
                "Checked device_12 and rule-4a; impactToken=abc123 confirms nothing.");

        assertFalse(presented.contains("device_12"));
        assertFalse(presented.contains("rule-4a"));
        assertFalse(presented.contains("abc123"));
        assertTrue(presented.contains("[internal reference]"));
        assertTrue(presented.contains("[hidden]"));
    }

    @Test
    void overlongReasoningIsCutAtASentenceBoundaryRatherThanMidClause() {
        String sentence = "The kitchen sensor constrains the heater rule in a way that matters. ";
        String presented = presenter.compactReasoningProgressDetail(sentence.repeat(60));

        assertTrue(presented.endsWith("…"));
        // A boundary cut leaves a complete sentence before the ellipsis.
        assertTrue(presented.contains("matters."), "expected a whole sentence, got: " + presented);
        assertFalse(presented.contains("matter. The kitchen sensor constrains the heater rule in a w"),
                "a mid-word cut means the boundary search did not run");
    }

    @Test
    void underscoreIdentifiersAreRedactedEvenWithoutADigit() {
        // A node id need not be numeric, and English prose does not join words with underscores, so
        // requiring a digit in the tail leaked every non-numeric id past the only mechanical guard.
        String presented = presenter.compactReasoningProgressDetail(
                "Compared device_a with spec_x and rule_ab.");

        assertFalse(presented.contains("device_a"));
        assertFalse(presented.contains("spec_x"));
        assertFalse(presented.contains("rule_ab"));
    }

    @Test
    void aLongUnbrokenParagraphTakesTheHardCutRatherThanLosingMostOfTheText() {
        // The boundary search is gated to the last third on purpose: here the only boundary sits at
        // character ~24, so honouring it would discard almost the whole explanation to end on a
        // period. The hard cut keeps the reasoning and marks itself with an ellipsis.
        String presented = presenter.compactReasoningProgressDetail(
                "First, decide the scope.\n" + "and then reason at length ".repeat(120));

        assertTrue(presented.endsWith("…"));
        assertTrue(presented.length() > 1000, "length: " + presented.length());
        assertTrue(presented.startsWith("First, decide the scope."));
    }

    @Test
    void reasoningGetsAMeaningfullyLargerBudgetThanAToolStatusLine() {
        String filler = "x".repeat(4000);
        assertTrue(presenter.compactReasoningProgressDetail(filler).length()
                > presenter.compactProgressDetail(filler).length() * 4);
    }
}
