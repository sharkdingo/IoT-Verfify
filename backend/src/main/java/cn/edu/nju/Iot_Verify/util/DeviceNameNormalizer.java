package cn.edu.nju.Iot_Verify.util;

/**
 * Canonicalizes a device reference the same way the frontend does before it snapshots a
 * verification request (see {@code normalizeDeviceName} in {@code Board.vue}).
 *
 * <p>NuSMV identifiers cannot start with a digit, so the frontend prefixes such labels with
 * {@code d_} <em>before</em> sending devices/rules/specs for verification. Rules and specs are,
 * however, persisted with the <em>raw</em> label (e.g. {@code 1Lamp}). When the fix flow later
 * compares the persisted board against a trace's verification-time snapshot, the two sides name the
 * same device differently ({@code 1Lamp} vs {@code d_1Lamp}) and a naive comparison misfires.</p>
 *
 * <p>Applying this normalizer to both sides before device-name resolution makes them line up.
 * It is idempotent: an already-normalized name ({@code d_1Lamp}, {@code Lamp}) is returned
 * unchanged.</p>
 */
public final class DeviceNameNormalizer {

    private DeviceNameNormalizer() {}

    /**
     * Mirror of the frontend transform: prefix with {@code d_} when the name starts with a digit,
     * otherwise return it unchanged. Null/blank inputs are returned as-is.
     */
    public static String normalize(String name) {
        if (name == null || name.isEmpty()) {
            return name;
        }
        char first = name.charAt(0);
        if (first >= '0' && first <= '9') {
            return "d_" + name;
        }
        return name;
    }
}
