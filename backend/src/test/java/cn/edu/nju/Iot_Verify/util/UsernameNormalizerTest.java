package cn.edu.nju.Iot_Verify.util;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class UsernameNormalizerTest {

    @Test
    void normalize_shouldStripUnicodeWhitespaceAndComposeUnicode() {
        assertEquals("Caf\u00e9", UsernameNormalizer.normalize("\u00a0\u2003Cafe\u0301\u2003\u00a0"));
    }

    @Test
    void isValid_shouldCountCodePointsAndRejectInvisibleControlCharacters() {
        assertTrue(UsernameNormalizer.isValid("Alice"));
        assertTrue(UsernameNormalizer.isValid("\ud83d\udca1\ud83c\udfe0\ud83d\udd12"));
        assertFalse(UsernameNormalizer.isValid("Ali\nce"));
        assertFalse(UsernameNormalizer.isValid("Ali\u2028ce"));
        assertFalse(UsernameNormalizer.isValid("Ali\u200bce"));
    }
}
