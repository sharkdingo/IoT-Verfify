package cn.edu.nju.Iot_Verify.util;

import java.util.Locale;
import java.util.Set;

/**
 * Canonicalizes a board node id into the NuSMV-safe device variable name used by
 * verification, simulation, traces, and fix logic.
 *
 * <p>The frontend mirrors this function in {@code frontend/src/utils/modelRequest.ts}.
 * Persisted board data keeps the raw {@code DeviceNode.id}; NuSMV requests and traces use this
 * normalized form.</p>
 *
 * <p>The function is intentionally not a label resolver. Labels and template names are display
 * metadata and must not be used as identity fallback.</p>
 */
public final class DeviceNameNormalizer {

    private DeviceNameNormalizer() {}

    public static final Set<String> NUSMV_RESERVED_WORDS = Set.of(
            "MODULE", "VAR", "IVAR", "FROZENVAR", "DEFINE", "CONSTANTS", "ASSIGN",
            "INIT", "TRANS", "INVAR", "INVARS", "SPEC", "CTLSPEC", "LTLSPEC",
            "FAIRNESS", "COMPASSION", "JUSTICE", "ISA", "FUN", "PRED",
            "MIRROR", "INVARSPEC", "COMPUTE",
            "case", "esac", "next", "init", "self",
            "TRUE", "FALSE", "boolean", "integer", "word", "signed", "unsigned",
            "process", "array", "of", "mod", "union", "in", "xor", "xnor",
            "abs", "max", "min", "count", "toint", "typeof",
            "swconst", "wordconst", "uwconst", "resize", "extend",
            "signed_word", "unsigned_word",
            "EX", "AX", "EF", "AF", "EG", "AG",
            "E", "F", "O", "G", "H", "X", "Y", "Z", "W", "A", "U", "S", "V", "T",
            "BU", "EBF", "ABF", "EBG", "ABG"
    );

    /**
     * Convert a raw board node id to a NuSMV-safe identifier.
     * Null/empty inputs are returned as-is so callers can distinguish absent references.
     */
    public static String normalize(String name) {
        if (name == null || name.isEmpty()) {
            return name;
        }
        String normalized = name.replaceAll("[^a-zA-Z0-9_]", "_").toLowerCase(Locale.ROOT);
        if (normalized.isEmpty() || normalized.matches("^_+$")) {
            normalized = "device_0";
        }
        if (Character.isDigit(normalized.charAt(0))) {
            normalized = "_" + normalized;
        }
        if (NUSMV_RESERVED_WORDS.contains(normalized)
                || NUSMV_RESERVED_WORDS.contains(normalized.toUpperCase(Locale.ROOT))) {
            normalized = "_" + normalized;
        }
        return normalized;
    }
}
