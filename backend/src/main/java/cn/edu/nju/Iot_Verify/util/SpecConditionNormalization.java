package cn.edu.nju.Iot_Verify.util;

import java.util.Locale;

/**
 * How the admission boundaries canonicalize a specification condition's discriminator fields.
 *
 * <p>Board storage and the verification request validator are deliberately independent writer boundaries
 * with different error text and different audiences, and that stays true. What must NOT differ is how they
 * fold a value: if one accepts {@code " Environment "} as {@code environment} and the other does not, the
 * same authored condition is admitted by one path and refused by the other, and a specification can be
 * stored in a shape the generator will not compile. These three methods were hand-copied into both classes
 * — {@code normalizePropertyScope} first, then {@code variableSource} followed it — so the drift hazard was
 * demonstrated rather than hypothetical.
 *
 * <p>Scope, stated precisely because an earlier version of this comment overclaimed: this owns the folding
 * used by the two <em>admission</em> boundaries — board storage and the verification request validator. The
 * generator keeps its own target-type normalizer on purpose (see {@link #knownSpecTargetType}), and the rule
 * tools fold their own condition shapes, which are not specification conditions.
 *
 * <p>Each method returns {@code null} for absent, blank, and unrecognised input alike. Callers that need to
 * tell "not supplied" from "supplied but invalid" must check the raw value first; the two have different
 * meanings for {@code variableSource} in particular, where absent means the author never chose.
 */
public final class SpecConditionNormalization {

    private static final java.util.Set<String> SPEC_TARGET_TYPES =
            java.util.Set.of("state", "mode", "variable", "api", "trust", "privacy");

    private SpecConditionNormalization() {
    }

    /** {@code state} or {@code variable}; null if absent, blank, or anything else. */
    public static String propertyScope(String value) {
        return oneOf(value, "state", "variable");
    }

    /**
     * {@code environment} (the shared pool value) or {@code reported} (what this device said); null if
     * absent, blank, or anything else.
     */
    public static String variableSource(String value) {
        return oneOf(value, "environment", "reported");
    }

    /**
     * A condition target type folded to one of the six the authored contract allows; null if absent, blank,
     * or anything else, so a caller can raise a validation error on it.
     *
     * <p>Note what is NOT here: the generator's own normalizer deliberately does not restrict membership,
     * because it must fail closed with the unrecognised value quoted back rather than turn it into a null
     * that reads as "absent". Two different jobs, kept separate on purpose.
     */
    public static String knownSpecTargetType(String value) {
        if (value == null || value.isBlank()) {
            return null;
        }
        String normalized = value.trim().toLowerCase(Locale.ROOT);
        return SPEC_TARGET_TYPES.contains(normalized) ? normalized : null;
    }

    private static String oneOf(String value, String first, String second) {
        if (value == null || value.isBlank()) {
            return null;
        }
        String normalized = value.trim().toLowerCase(Locale.ROOT);
        return first.equals(normalized) || second.equals(normalized) ? normalized : null;
    }
}
