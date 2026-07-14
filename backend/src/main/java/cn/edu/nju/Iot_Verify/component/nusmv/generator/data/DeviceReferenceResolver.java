package cn.edu.nju.Iot_Verify.component.nusmv.generator.data;

import java.util.Map;

/**
 * Resolves canonical board device instance ids against the verification-time device map.
 */
public final class DeviceReferenceResolver {

    private DeviceReferenceResolver() {}

    public static DeviceSmvData resolve(String deviceId, Map<String, DeviceSmvData> deviceSmvMap) {
        if (deviceSmvMap == null || deviceSmvMap.isEmpty()) {
            return null;
        }
        String ref = trimToNull(deviceId);
        if (ref == null) {
            return null;
        }
        return deviceSmvMap.get(ref);
    }

    /**
     * Return the canonical reference that should be written into generated rule candidates.
     */
    public static String resolvableReference(String deviceId, Map<String, DeviceSmvData> deviceSmvMap) {
        String ref = trimToNull(deviceId);
        if (ref == null) {
            return null;
        }
        return resolve(ref, deviceSmvMap) != null ? ref : null;
    }

    public static String canonicalReference(String deviceId, Map<String, DeviceSmvData> deviceSmvMap) {
        String ref = resolvableReference(deviceId, deviceSmvMap);
        return ref;
    }

    private static String trimToNull(String value) {
        if (value == null) {
            return null;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }
}
