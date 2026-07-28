package cn.edu.nju.Iot_Verify.util;

import org.junit.jupiter.api.Test;

import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The template-name rule exists to keep case-insensitive uniqueness comparable between Java and
 * MySQL — not to restrict the alphabet a user may name a device template in.
 */
class TemplateNameRuleTest {

    @Test
    void acceptsOrdinaryAsciiNames() {
        assertTrue(TemplateNameRule.isSafe("Smoke Sensor"));
        assertTrue(TemplateNameRule.isSafe("AC-2 (living room)"));
    }

    @Test
    void acceptsCaselessScripts() {
        // These have no case, so lowercasing is the identity in both engines. Rejecting them was a
        // pure usability loss: device labels on the same board already accept any Unicode.
        assertTrue(TemplateNameRule.isSafe("温度传感器"), "Chinese template names are legitimate");
        assertTrue(TemplateNameRule.isSafe("エアコン"), "Japanese template names are legitimate");
        assertTrue(TemplateNameRule.isSafe("스모크 센서"), "Korean template names are legitimate");
    }

    @Test
    void stillRejectsCasedNonAsciiLetters() {
        // The actual parity risk: a cased letter outside ASCII may fold differently in MySQL.
        assertFalse(TemplateNameRule.isSafe("Wärmepumpe"));
        assertFalse(TemplateNameRule.isSafe("İstanbul"));
        assertFalse(TemplateNameRule.isSafe("ẛ"));
    }

    @Test
    void rejectsControlCharactersAndEmptyNames() {
        assertFalse(TemplateNameRule.isSafe(null));
        assertFalse(TemplateNameRule.isSafe(""));
        assertFalse(TemplateNameRule.isSafe("Heater\tunit"));
        assertFalse(TemplateNameRule.isSafe("Heater\nunit"));
        assertTrue(TemplateNameRule.isSafe("Heater unit"), "a plain space is allowed");
    }

    @Test
    void namesTheConstraintThatActuallyFailed() {
        // Callers build their user-facing message from this, so a tab must not be reported as a
        // non-ASCII problem and vice versa.
        assertTrue(TemplateNameRule.rejectionReason("Heater\tunit").contains("control characters"));
        assertTrue(TemplateNameRule.rejectionReason("Wärmepumpe").contains("cased non-ASCII"));
        assertTrue(TemplateNameRule.rejectionReason("").contains("empty"));
        assertEquals(null, TemplateNameRule.rejectionReason("温度传感器"));
    }

    @Test
    void everyAcceptedNameLowercasesIdempotentlyUnderRootLocale() {
        // The invariant the rule is actually protecting: for an accepted name, Java's Locale.ROOT
        // lowercase must equal a per-character lowercase, which is what MySQL LOWER() approximates.
        for (String name : new String[]{"Smoke Sensor", "温度传感器", "エアコン", "AC-2 (living room)"}) {
            StringBuilder perCharacter = new StringBuilder();
            for (char character : name.toCharArray()) {
                perCharacter.append(Character.toLowerCase(character));
            }
            assertEquals(perCharacter.toString(), name.toLowerCase(Locale.ROOT),
                    "case folding must agree for accepted name: " + name);
        }
    }
}
