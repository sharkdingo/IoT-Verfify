package cn.edu.nju.Iot_Verify.component.fuzz;

/** Shared bounds and normalization for persisted/user-facing fuzz metadata. */
public final class FuzzMetadataPolicy {

    public static final long MAX_RUN_METADATA_BYTES = 256L * 1024;
    public static final int MAX_ELIGIBILITY_LABEL_CHARS = 200;
    public static final int MAX_ELIGIBILITY_REASON_CHARS = 500;
    public static final int MAX_STABLE_CODE_CHARS = 100;
    public static final int MAX_LIMITATION_CODES = 32;

    private FuzzMetadataPolicy() {
    }

    public static String boundedSingleLine(String value, String fallback, int maxChars) {
        String source = hasText(value) ? value : fallback;
        if (!hasText(source) || maxChars < 4) {
            throw new IllegalArgumentException(
                    "A non-blank fallback and at least four characters are required");
        }
        StringBuilder normalized = new StringBuilder(Math.min(source.length(), maxChars));
        boolean pendingSpace = false;
        boolean truncated = false;
        int index = 0;
        int contentLimit = maxChars - 3;
        while (index < source.length() && normalized.length() < contentLimit) {
            int codePoint = source.codePointAt(index);
            int codePointChars = Character.charCount(codePoint);
            if (Character.isWhitespace(codePoint) || Character.isISOControl(codePoint)) {
                index += codePointChars;
                pendingSpace = normalized.length() > 0;
                continue;
            }
            if (pendingSpace && normalized.length() < contentLimit) {
                normalized.append(' ');
            }
            pendingSpace = false;
            if (normalized.length() + codePointChars > contentLimit) {
                truncated = true;
                break;
            }
            normalized.appendCodePoint(codePoint);
            index += codePointChars;
        }
        if (index < source.length()) truncated = true;
        if (truncated) {
            normalized.append("...");
        }
        String result = normalized.toString().trim();
        return result.isEmpty()
                ? boundedSingleLine(fallback, "Unavailable", maxChars)
                : result;
    }

    private static boolean hasText(String value) {
        return value != null && !value.isBlank();
    }
}
