package cn.edu.nju.Iot_Verify.component.ai;

import org.springframework.stereotype.Component;

import java.util.Locale;
import java.util.regex.Pattern;

/** Detects explicit user confirmation for destructive two-turn tool operations. */
@Component
public class ChatConfirmationDetector {

    private static final Pattern ENGLISH_CONFIRMATION = pattern(
            "^(yes|y|confirm(?:ed)?|i confirm(?: .+)?|yes[, ]+.+|proceed(?: .+)?|go ahead(?: .+)?|delete it|do it)[.! ]*$");
    private static final Pattern CHINESE_CONFIRMATION = pattern(
            "^(?:\\u662f\\u7684[\\uff0c, ]*)?(?:\\u6211)?(?:\\u786e\\u8ba4|\\u786e\\u5b9a|\\u540c\\u610f|\\u7ee7\\u7eed)(?:\\u5220\\u9664|\\u6267\\u884c|\\u5e94\\u7528)?[^?\\uff1f]{0,80}[\\u3002\\uff01! ]*$|^(?:\\u5220\\u9664|\\u6267\\u884c)\\u5427[\\u3002\\uff01! ]*$");
    private static final Pattern CONFIRMATION_NEGATION = pattern(
            "\\b(no|not|don't|do not|cancel|stop|wait)\\b|\\u4e0d\\u8981|\\u4e0d\\u786e\\u8ba4|\\u53d6\\u6d88|\\u5148\\u522b|\\u7b49\\u7b49|\\u505c\\u6b62");

    public boolean isExplicitConfirmation(String content) {
        if (content == null || content.isBlank()) return false;
        String normalized = content.trim().toLowerCase(Locale.ROOT).replaceAll("\\s+", " ");
        if (normalized.length() > 160
                || normalized.contains("?")
                || normalized.contains("\uff1f")
                || CONFIRMATION_NEGATION.matcher(normalized).find()) {
            return false;
        }
        return ENGLISH_CONFIRMATION.matcher(normalized).matches()
                || CHINESE_CONFIRMATION.matcher(normalized).matches();
    }

    private static Pattern pattern(String regex) {
        return Pattern.compile(regex, Pattern.CASE_INSENSITIVE | Pattern.UNICODE_CASE);
    }
}
