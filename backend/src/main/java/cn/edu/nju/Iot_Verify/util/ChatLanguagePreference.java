package cn.edu.nju.Iot_Verify.util;

import java.util.Locale;

/**
 * Which language a chat turn's backend-authored prose is written in.
 *
 * <p>The client's declared UI locale decides it. Inspecting the user's message is only the fallback for a request
 * that sends none, and it is a poor one: it reports English for every message carrying no Han character, so a
 * Chinese interface asked "hi" answered with English status prose. The language a user *reads* is not a property
 * of the sentence they typed — device ids, English product names and ordinary greetings all carry no Han
 * character, and each produced the wrong language.
 *
 * <p>One owner because there were two: {@code ChatServiceImpl} chose the language for execution notices, error
 * text and interruption audits, while {@code ChatController} carried its own copy of the same code-point scan for
 * the admission-outcome-unknown warning. Two copies of a language decision drift into two answers for one turn,
 * and the controller's message — "rollback could not be confirmed" — is among the least affordable to get wrong.
 */
public final class ChatLanguagePreference {

    private ChatLanguagePreference() {
    }

    /**
     * @param locale  BCP 47 tag from the client ({@code zh-CN} / {@code en}); null or blank falls back to
     *                {@code content}
     * @param content the user's message, inspected only as that fallback
     */
    public static boolean prefersChinese(String locale, String content) {
        if (locale != null && !locale.isBlank()) {
            // The `zh` language subtag rather than the full tag, so zh-CN, zh-TW and a bare zh all agree.
            // Locale.ROOT pins the fold: this decides a keyword, and a Turkish default folds `I` to a dotless `ı`.
            return locale.trim().toLowerCase(Locale.ROOT).startsWith("zh");
        }
        return content != null && content.codePoints().anyMatch(codePoint ->
                Character.UnicodeScript.of(codePoint) == Character.UnicodeScript.HAN);
    }
}
