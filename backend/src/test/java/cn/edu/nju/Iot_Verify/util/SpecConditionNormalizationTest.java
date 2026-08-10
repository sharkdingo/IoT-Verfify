package cn.edu.nju.Iot_Verify.util;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Board storage and the verification request validator are independent writer boundaries with their own
 * error text, but they must fold a value identically: if one accepted {@code " Environment "} and the other
 * did not, the same authored condition would be admitted by one path and refused by the other, and a
 * specification could be stored in a shape the generator will not compile. These methods were hand-copied
 * into both classes before this owner existed, so the drift hazard was demonstrated, not hypothetical.
 */
class SpecConditionNormalizationTest {

    @Test
    void variableSource_acceptsBothReadingsInAnyCasingOrPadding() {
        assertEquals("environment", SpecConditionNormalization.variableSource("environment"));
        assertEquals("environment", SpecConditionNormalization.variableSource("  Environment  "));
        assertEquals("environment", SpecConditionNormalization.variableSource("ENVIRONMENT"));
        assertEquals("reported", SpecConditionNormalization.variableSource("Reported"));
    }

    @Test
    void variableSource_collapsesAbsentBlankAndUnrecognisedToNull() {
        // One null for three distinct inputs is deliberate, and callers that must tell "never chose" from
        // "chose something invalid" check the raw value first — the distinction is load-bearing only for
        // variableSource, where absent means the author was never asked.
        assertNull(SpecConditionNormalization.variableSource(null));
        assertNull(SpecConditionNormalization.variableSource("   "));
        assertNull(SpecConditionNormalization.variableSource("pool"));
        assertNull(SpecConditionNormalization.variableSource("environment reported"));
    }

    @Test
    void propertyScope_behavesTheSameWayForItsOwnTwoLiterals() {
        assertEquals("state", SpecConditionNormalization.propertyScope(" State "));
        assertEquals("variable", SpecConditionNormalization.propertyScope("VARIABLE"));
        assertNull(SpecConditionNormalization.propertyScope("mode"));
        assertNull(SpecConditionNormalization.propertyScope(null));
    }

    @Test
    void knownSpecTargetType_foldsTheSixAllowedTypesAndRejectsTheRest() {
        /*
         * Restricts membership, unlike the generator's own normalizer: an admission boundary needs null for
         * an unknown type so it can raise a validation error, while the generator needs to fail closed with
         * the unrecognised value quoted back. Two jobs, deliberately not shared — this method exists because
         * the two admission boundaries had byte-identical copies of THIS one.
         */
        assertEquals("variable", SpecConditionNormalization.knownSpecTargetType(" Variable "));
        assertEquals("privacy", SpecConditionNormalization.knownSpecTargetType("PRIVACY"));
        for (String allowed : new String[]{"state", "mode", "variable", "api", "trust", "privacy"}) {
            assertEquals(allowed, SpecConditionNormalization.knownSpecTargetType(allowed));
        }
        assertNull(SpecConditionNormalization.knownSpecTargetType("something-else"));
        assertNull(SpecConditionNormalization.knownSpecTargetType("  "));
        assertNull(SpecConditionNormalization.knownSpecTargetType(null));
    }
}
