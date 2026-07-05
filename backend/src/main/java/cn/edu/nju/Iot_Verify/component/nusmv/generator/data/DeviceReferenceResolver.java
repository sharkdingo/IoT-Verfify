package cn.edu.nju.Iot_Verify.component.nusmv.generator.data;

import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.util.DeviceNameNormalizer;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Resolves user-facing device references against the verification-time device map.
 *
 * <p>Different entry points legitimately carry different identifiers: browser requests use the current
 * device label (with {@code d_} added for digit-leading labels), persisted specs may still carry a
 * legacy node id plus a label, and AI tools can supply either. Keeping that fallback order in one
 * place prevents the generator, fixer, and drift checks from silently disagreeing.</p>
 */
public final class DeviceReferenceResolver {

    private DeviceReferenceResolver() {}

    public static DeviceSmvData resolve(String primaryRef, String secondaryRef,
                                        Map<String, DeviceSmvData> deviceSmvMap) {
        if (deviceSmvMap == null || deviceSmvMap.isEmpty()) {
            return null;
        }

        SmvGenerationException ambiguous = null;
        for (String ref : candidateRefs(primaryRef, secondaryRef)) {
            DeviceSmvData exact = deviceSmvMap.get(ref);
            if (exact != null) {
                return exact;
            }
            try {
                DeviceSmvData resolved = DeviceSmvDataFactory.findDeviceSmvDataStrict(ref, deviceSmvMap);
                if (resolved != null) {
                    return resolved;
                }
            } catch (SmvGenerationException e) {
                if (SmvGenerationException.ErrorCategories.AMBIGUOUS_DEVICE_REFERENCE.equals(e.getErrorCategory())) {
                    ambiguous = e;
                } else {
                    throw e;
                }
            }
        }
        if (ambiguous != null) {
            throw ambiguous;
        }
        return null;
    }

    /**
     * Return the input reference that should be written into generated rule candidates. Prefer a
     * resolvable raw/canonical reference over the SMV varName so persisted rules stay close to board
     * labels where possible.
     */
    public static String resolvableReference(String primaryRef, String secondaryRef,
                                             Map<String, DeviceSmvData> deviceSmvMap) {
        if (deviceSmvMap == null || deviceSmvMap.isEmpty()) {
            return firstNonBlank(primaryRef, secondaryRef);
        }
        SmvGenerationException ambiguous = null;
        for (String ref : candidateRefs(primaryRef, secondaryRef)) {
            if (deviceSmvMap.get(ref) != null) {
                return ref;
            }
            try {
                DeviceSmvData resolved = DeviceSmvDataFactory.findDeviceSmvDataStrict(ref, deviceSmvMap);
                if (resolved != null) {
                    return ref;
                }
            } catch (SmvGenerationException e) {
                if (SmvGenerationException.ErrorCategories.AMBIGUOUS_DEVICE_REFERENCE.equals(e.getErrorCategory())) {
                    ambiguous = e;
                } else {
                    throw e;
                }
            }
        }
        if (ambiguous != null) {
            throw ambiguous;
        }
        return firstNonBlank(primaryRef, secondaryRef);
    }

    public static String canonicalReference(String primaryRef, String secondaryRef,
                                            Map<String, DeviceSmvData> deviceSmvMap) {
        String ref = resolvableReference(primaryRef, secondaryRef, deviceSmvMap);
        return DeviceNameNormalizer.normalize(ref);
    }

    private static List<String> candidateRefs(String primaryRef, String secondaryRef) {
        Set<String> refs = new LinkedHashSet<>();
        addRef(refs, primaryRef);
        addRef(refs, secondaryRef);
        return new ArrayList<>(refs);
    }

    private static void addRef(Set<String> refs, String ref) {
        String trimmed = trimToNull(ref);
        if (trimmed == null) {
            return;
        }
        refs.add(trimmed);
        String normalized = DeviceNameNormalizer.normalize(trimmed);
        if (normalized != null && !normalized.isBlank()) {
            refs.add(normalized);
        }
    }

    private static String firstNonBlank(String first, String second) {
        String v = trimToNull(first);
        return v != null ? v : trimToNull(second);
    }

    private static String trimToNull(String value) {
        if (value == null) {
            return null;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }
}
