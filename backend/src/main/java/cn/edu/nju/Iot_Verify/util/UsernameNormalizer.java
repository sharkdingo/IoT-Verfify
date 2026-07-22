package cn.edu.nju.Iot_Verify.util;

import java.text.Normalizer;

public final class UsernameNormalizer {

    private static final String PHONE_PATTERN = "^1[3-9]\\d{9}$";

    private UsernameNormalizer() {
    }

    public static String normalize(String value) {
        if (value == null) return "";
        String normalized = Normalizer.normalize(value, Normalizer.Form.NFC);
        int start = 0;
        int end = normalized.length();
        while (start < end) {
            int codePoint = normalized.codePointAt(start);
            if (!isEdgeWhitespace(codePoint)) break;
            start += Character.charCount(codePoint);
        }
        while (end > start) {
            int codePoint = normalized.codePointBefore(end);
            if (!isEdgeWhitespace(codePoint)) break;
            end -= Character.charCount(codePoint);
        }
        return normalized.substring(start, end);
    }

    public static boolean isValid(String value) {
        if (value == null) return false;
        int length = value.codePointCount(0, value.length());
        if (length < 3 || length > 20) return false;
        return value.codePoints().noneMatch(codePoint ->
                Character.isISOControl(codePoint)
                        || Character.getType(codePoint) == Character.FORMAT
                        || Character.getType(codePoint) == Character.LINE_SEPARATOR
                        || Character.getType(codePoint) == Character.PARAGRAPH_SEPARATOR);
    }

    public static boolean isPhoneNumber(String value) {
        return value != null && value.matches(PHONE_PATTERN);
    }

    private static boolean isEdgeWhitespace(int codePoint) {
        return Character.isWhitespace(codePoint) || Character.isSpaceChar(codePoint);
    }
}
