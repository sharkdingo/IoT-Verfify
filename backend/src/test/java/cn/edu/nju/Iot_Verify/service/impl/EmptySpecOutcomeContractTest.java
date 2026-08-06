package cn.edu.nju.Iot_Verify.service.impl;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run that checked nothing must not report SATISFIED.
 *
 * <p>The outcome is derived as {@code specResults.stream().allMatch(o == SATISFIED)}, and
 * {@code allMatch} is <b>vacuously true for an empty list</b>. So a run whose specifications were all filtered
 * out before SMV emission would label itself SATISFIED — the worst possible failure for a verification tool,
 * because "safe" is exactly the answer a user acts on without reading further.
 *
 * <p>The only thing preventing it is the early return above that computation, which reports INCONCLUSIVE with
 * {@code modelComplete=false}. {@code modelComplete} alone is not enough: it is a secondary field, and the
 * outcome label is what the UI colours and what the AI tools summarise.
 *
 * <p>Asserted against the source because reaching this branch behaviourally needs a specification that passes
 * the write boundary and is still dropped at generation. Every route tried against the live API was refused
 * earlier — an unknown condition device is 422, a wildcard state is 400 — so the branch is currently hard to
 * reach from outside, which is precisely why its guard needs pinning rather than trusting.
 */
class EmptySpecOutcomeContractTest {

    private static final Path SOURCE = Path.of(
            "src/main/java/cn/edu/nju/Iot_Verify/service/impl/VerificationServiceImpl.java");

    @Test
    @DisplayName("the empty-spec case returns INCONCLUSIVE before allMatch can be vacuously true")
    void emptySpecsShortCircuitToInconclusive() throws IOException {
        String source = Files.readString(SOURCE, StandardCharsets.UTF_8);

        int guard = source.indexOf("if (effectiveSpecs.isEmpty())");
        assertTrue(guard >= 0,
                "the empty-spec guard is gone; allMatch over an empty specResults reports SATISFIED for a run "
                        + "that verified nothing");

        int vacuous = source.indexOf("boolean allPassed");
        assertTrue(vacuous >= 0, "expected the allPassed derivation; this test is reading the wrong method");
        assertTrue(guard < vacuous,
                "the empty-spec guard must run before the allMatch derivation, otherwise a run with zero "
                        + "emitted specifications reaches it and is labelled SATISFIED");

        // The guard's body, up to the derivation it protects, must produce the inconclusive verdict itself.
        String body = source.substring(guard, vacuous);
        assertTrue(body.contains("outcome(VerificationOutcome.INCONCLUSIVE)"),
                "the empty-spec guard must set the outcome to INCONCLUSIVE, not rely on modelComplete=false "
                        + "being noticed by the reader");
        assertTrue(body.contains("modelComplete(false)"),
                "a run with no emitted specifications did not model the user's specifications");
    }
}
