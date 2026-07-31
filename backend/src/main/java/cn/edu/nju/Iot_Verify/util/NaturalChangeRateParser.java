package cn.edu.nju.Iot_Verify.util;

import java.util.ArrayList;
import java.util.List;
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

    /**
     * A declared per-step change interval.
     *
     * <p>The interval is a <em>constraint</em> on {@code v' - v}, exactly as MEDIC §3.1, Fig. 2b
     * writes it — not a shortlist of interesting deltas. Emitting only the endpoints was unsound:
     * for {@code [-3, 3]} it omitted ±1 and ±2, so NuSMV proved
     * {@code AG (v = 5 -> AX v != 6)} <em>true</em> for a variable the declaration lets reach 6 in
     * one step. A verifier must never report SATISFIED for behaviour the declaration permits, so
     * every integer in the interval is admitted. {@code [-1, 1]} is unchanged by this — it has no
     * interior — which is why the unsoundness stayed hidden while every bundled template used it.
     */
    public record RateRange(int lower, int upper) {

        /** True when the declaration permits no independent change at all. */
        public boolean isStatic() {
            return lower == 0 && upper == 0;
        }

        /**
         * Widest single-step magnitude the interval permits, as a long so {@code Integer.MIN_VALUE}
         * cannot overflow the comparison.
         */
        public long span() {
            return (long) upper - (long) lower;
        }

        /**
         * Every integer delta the declaration admits, ascending, always including {@code 0}.
         *
         * <p>Zero is always present because a step in which the value does not drift is permitted
         * even by an interval that excludes it arithmetically (for example {@code [1, 3]}): the
         * product treats a declared rate as the drift a step <em>may</em> apply, not one it must.
         * Callers combine each delta with the active device effect for that step.
         */
        public List<Integer> admissibleDeltas() {
            List<Integer> deltas = new ArrayList<>();
            for (int delta = lower; delta <= upper; delta++) {
                deltas.add(delta);
                if (delta == Integer.MAX_VALUE) break;
            }
            if (!deltas.contains(Integer.valueOf(0))) {
                deltas.add(lower > 0 ? 0 : deltas.size(), Integer.valueOf(0));
            }
            return List.copyOf(deltas);
        }
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
