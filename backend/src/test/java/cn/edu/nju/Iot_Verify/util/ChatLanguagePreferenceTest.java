package cn.edu.nju.Iot_Verify.util;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import static cn.edu.nju.Iot_Verify.util.ChatLanguagePreference.prefersChinese;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The language of the assistant's backend-authored prose comes from the client's UI locale, not the user's words.
 *
 * <p>It used to come only from the words: a code-point scan for a Han character in the message. So a user reading
 * a Chinese interface who typed "hi" received English status prose beside a Chinese badge. The text a user types
 * is not evidence of the language they read — device ids, English product names and ordinary greetings all carry
 * no Han character, and every one produced the wrong language.
 */
class ChatLanguagePreferenceTest {

    @Test
    @DisplayName("a declared locale outranks the message text, in both directions")
    void localeDecidesOverMessageText() {
        // The exact reported defect: interface Chinese, message "hi".
        assertTrue(prefersChinese("zh-CN", "hi"));
        assertTrue(prefersChinese("zh", "hi"));
        assertTrue(prefersChinese("zh-TW", "Thermostat"));
        // The mirror: an English UI is not flipped by a Chinese quotation inside the message.
        assertFalse(prefersChinese("en", "他说 hello"));
        assertFalse(prefersChinese("en-US", "温控器"));
    }

    @Test
    @DisplayName("no declared locale falls back to the message, rather than assuming English")
    void absentLocaleFallsBackToTextInspection() {
        // A client that sends no locale must keep the old behaviour. A guess is worse than a declaration, but
        // silently calling it English would regress every Chinese request that previously worked.
        assertTrue(prefersChinese(null, "请列出规则"));
        assertTrue(prefersChinese("", "请列出规则"));
        assertTrue(prefersChinese("   ", "请列出规则"));
        assertFalse(prefersChinese(null, "list the rules"));
        assertFalse(prefersChinese(null, null));
    }

    @Test
    @DisplayName("the locale match tolerates case and surrounding space")
    void localeMatchIsCaseInsensitive() {
        // A tag arrives in whatever case the client wrote it. `Locale.ROOT` is required rather than stylistic:
        // this fold decides a keyword, and a Turkish default locale folds `I` to a dotless `ı`.
        assertTrue(prefersChinese("ZH-CN", "hi"));
        assertTrue(prefersChinese("Zh", "hi"));
        assertTrue(prefersChinese("  zh-CN  ", "hi"));
    }
}
