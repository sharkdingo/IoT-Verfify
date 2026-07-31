package cn.edu.nju.Iot_Verify.util;

import java.util.regex.Pattern;

/**
 * Parses the single canonical NaturalChangeRate grammar used by the template schema and both
 * model engines. A missing property means no declared natural change for local variables; a
 * present property must use an integer or a bracketed ordered integer interval.
 */
public final class NaturalChangeRateParser {

    private static final Pattern CANONICAL_SYNTAX = Pattern.compile(
            "(?:-?[0-9]+|\\[\\s*-?[0-9]+\\s*,\\s*-?[0-9]+\\s*\\])");

    private NaturalChangeRateParser() {
    }

    /** Parse a nullable declaration; null is the omitted local-variable declaration. */
    public static RateRange parse(String raw) {
        if (raw == null) {
            return new RateRange(0, 0);
        }
        if (!CANONICAL_SYNTAX.matcher(raw).matches()) {
            throw new ParseException(false);
        }
        String body = raw.startsWith("[")
                ? raw.substring(1, raw.length() - 1)
                : raw;
        String[] parts = body.split(",", -1);
        try {
            if (parts.length == 1) {
                int rate = Integer.parseInt(parts[0].trim());
                return rate < 0 ? new RateRange(rate, 0) : new RateRange(0, rate);
            }
            int lower = Integer.parseInt(parts[0].trim());
            int upper = Integer.parseInt(parts[1].trim());
            if (lower > upper) {
                throw new ParseException(true);
            }
            return new RateRange(lower, upper);
        } catch (NumberFormatException exception) {
            throw new ParseException(false);
        }
    }

    public static String canonical(String raw) {
        try {
            RateRange range = parse(raw);
            return range.lower() + ".." + range.upper();
        } catch (ParseException exception) {
            return raw == null ? "0..0" : raw.trim();
        }
    }

    public record RateRange(int lower, int upper) {
    }

    public static final class ParseException extends IllegalArgumentException {
        private final boolean descending;

        private ParseException(boolean descending) {
            super(descending ? "NaturalChangeRate lower bound exceeds upper bound"
                    : "NaturalChangeRate must be an integer or [lower, upper] using 32-bit integers");
            this.descending = descending;
        }

        public boolean isDescending() {
            return descending;
        }
    }
}
