package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;

import java.util.Locale;
import java.util.Objects;

/** Shared-environment domain resolution without implying device read capability. */
public final class EnvironmentDomainUtils {

    private EnvironmentDomainUtils() {
    }

    public static DeviceManifest.InternalVariable resolveImpactDomain(DeviceManifest manifest, String name) {
        if (manifest == null || name == null || name.isBlank()) {
            return null;
        }
        String target = name.trim();
        if (manifest.getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable variable : manifest.getInternalVariables()) {
                if (variable != null
                        && target.equals(variable.getName())
                        && !Boolean.TRUE.equals(variable.getIsInside())) {
                    return variable;
                }
            }
        }
        if (manifest.getEnvironmentDomains() != null) {
            for (DeviceManifest.EnvironmentDomain domain : manifest.getEnvironmentDomains()) {
                if (domain != null && target.equals(domain.getName())) {
                    return asInternalVariable(domain);
                }
            }
        }
        return null;
    }

    public static DeviceManifest.InternalVariable asInternalVariable(DeviceManifest.EnvironmentDomain domain) {
        if (domain == null) {
            return null;
        }
        return DeviceManifest.InternalVariable.builder()
                .name(domain.getName())
                .description(domain.getDescription())
                .isInside(false)
                .falsifiableWhenCompromised(false)
                .trust(domain.getTrust())
                .privacy(domain.getPrivacy())
                .lowerBound(domain.getLowerBound())
                .upperBound(domain.getUpperBound())
                .naturalChangeRate(domain.getNaturalChangeRate())
                .values(domain.getValues())
                .build();
    }

    /** Returns a user-facing semantic mismatch, or {@code null} when domains are equivalent. */
    public static String incompatibility(DeviceManifest.InternalVariable left,
                                         DeviceManifest.InternalVariable right) {
        if (left == null || right == null) {
            return "one declaration has no domain";
        }
        boolean leftEnum = hasValues(left);
        boolean rightEnum = hasValues(right);
        boolean leftNumeric = hasBounds(left);
        boolean rightNumeric = hasBounds(right);
        if (leftEnum != rightEnum || leftNumeric != rightNumeric) {
            return "type mismatch (" + describeType(left) + " versus " + describeType(right) + ")";
        }
        if (leftNumeric && (!Objects.equals(left.getLowerBound(), right.getLowerBound())
                || !Objects.equals(left.getUpperBound(), right.getUpperBound()))) {
            return "range mismatch (" + left.getLowerBound() + ".." + left.getUpperBound()
                    + " versus " + right.getLowerBound() + ".." + right.getUpperBound() + ")";
        }
        if (leftEnum && !Objects.equals(left.getValues(), right.getValues())) {
            return "enum values/order mismatch (" + left.getValues() + " versus " + right.getValues() + ")";
        }
        String leftRate = canonicalNaturalChangeRate(left.getNaturalChangeRate());
        String rightRate = canonicalNaturalChangeRate(right.getNaturalChangeRate());
        if (!leftRate.equals(rightRate)) {
            return "natural-change-rate mismatch (" + leftRate + " versus " + rightRate + ")";
        }
        String leftTrust = normalizeLabel(left.getTrust(), "untrusted");
        String rightTrust = normalizeLabel(right.getTrust(), "untrusted");
        if (!leftTrust.equals(rightTrust)) {
            return "default trust mismatch (" + leftTrust + " versus " + rightTrust + ")";
        }
        String leftPrivacy = normalizeLabel(left.getPrivacy(), "public");
        String rightPrivacy = normalizeLabel(right.getPrivacy(), "public");
        if (!leftPrivacy.equals(rightPrivacy)) {
            return "default privacy mismatch (" + leftPrivacy + " versus " + rightPrivacy + ")";
        }
        return null;
    }

    private static boolean hasValues(DeviceManifest.InternalVariable variable) {
        return variable.getValues() != null && !variable.getValues().isEmpty();
    }

    private static boolean hasBounds(DeviceManifest.InternalVariable variable) {
        return variable.getLowerBound() != null && variable.getUpperBound() != null;
    }

    private static String describeType(DeviceManifest.InternalVariable variable) {
        if (hasValues(variable)) return "enum" + variable.getValues();
        if (hasBounds(variable)) return variable.getLowerBound() + ".." + variable.getUpperBound();
        return "boolean";
    }

    private static String canonicalNaturalChangeRate(String raw) {
        if (raw == null || raw.isBlank()) {
            return "0..0";
        }
        String[] parts = raw.replace("[", "").replace("]", "").replace(" ", "").split(",");
        try {
            if (parts.length == 1) {
                int rate = Integer.parseInt(parts[0]);
                return Math.min(0, rate) + ".." + Math.max(0, rate);
            }
            if (parts.length == 2) {
                return Integer.parseInt(parts[0]) + ".." + Integer.parseInt(parts[1]);
            }
        } catch (NumberFormatException ignored) {
            // Schema validation reports malformed rates; preserve text here for deterministic mismatch reporting.
        }
        return raw.trim();
    }

    private static String normalizeLabel(String value, String fallback) {
        return value == null || value.isBlank() ? fallback : value.trim().toLowerCase(Locale.ROOT);
    }
}
