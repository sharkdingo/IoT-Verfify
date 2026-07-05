package cn.edu.nju.Iot_Verify.component.nusmv.fixer;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceReferenceResolver;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.util.DeviceNameNormalizer;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Produces a canonical, order-independent fingerprint of the <em>device instance state</em> and
 * <em>specifications</em> that feed NuSMV verification, so the fix-apply flow can detect whether the
 * user edited specs, device variables/privacies, or device initial state after verifying — drifts
 * that the server recompute (which replays the trace's stored context) can <b>not</b> catch on its
 * own.
 *
 * <h2>Why fingerprint instead of comparing raw JSON</h2>
 * The trace's stored request is a <em>frontend-transformed</em> snapshot: device varNames are
 * digit-prefixed ({@code 1Lamp} → {@code d_1Lamp}), and — critically — empty variable/privacy lists
 * are manifest-defaulted at verify time (a fresh device node stores neither). The current board read
 * back from storage has raw labels and possibly-empty variable/privacy lists. A byte-equality check
 * therefore misfires on untouched boards (this bug shipped once and was removed).
 *
 * <p>This class sidesteps that by running <b>both</b> sides through the <em>same</em> canonicalization
 * — normalize device names, manifest-default empty variable/privacy lists, strip quotes from numeric
 * values, lowercase trust/privacy — so any imperfection in the transform cancels out. An untouched
 * board and its snapshot canonicalize identically; a genuine edit changes the fingerprint on exactly
 * one side.</p>
 *
 * <p>Pure and deterministic (no NuSMV, no persistence), so it is unit-testable in isolation.</p>
 */
public final class BoardSemanticFingerprint {

    private BoardSemanticFingerprint() {}

    /**
     * Canonical fingerprint of the given devices + specs. {@code deviceSmvMap} supplies each device's
     * resolved manifest (used to default empty variable/privacy lists exactly as the frontend does).
     */
    public static String of(List<DeviceVerificationDto> devices,
                             List<SpecificationDto> specs,
                             Map<String, DeviceSmvData> deviceSmvMap) {
        return "devices{" + devicesFingerprint(devices, deviceSmvMap) + "}"
                + "specs{" + specsFingerprint(specs, deviceSmvMap) + "}";
    }

    // ==================== devices ====================

    private static String devicesFingerprint(List<DeviceVerificationDto> devices,
                                              Map<String, DeviceSmvData> deviceSmvMap) {
        if (devices == null || devices.isEmpty()) return "";
        List<String> parts = new ArrayList<>();
        for (DeviceVerificationDto d : devices) {
            if (d == null || d.getVarName() == null || d.getVarName().isBlank()) continue;
            parts.add(deviceFingerprint(d, deviceSmvMap));
        }
        parts.sort(String::compareTo);
        return String.join(";", parts);
    }

    private static String deviceFingerprint(DeviceVerificationDto d,
                                            Map<String, DeviceSmvData> deviceSmvMap) {
        String varName = DeviceNameNormalizer.normalize(d.getVarName());
        DeviceManifest manifest = manifestFor(varName, d.getVarName(), deviceSmvMap);

        StringBuilder sb = new StringBuilder();
        sb.append(varName)
          .append('|').append(nullSafe(d.getTemplateName()))
          .append('|').append(nullSafe(d.getState()))
          .append('|').append(normalizeTrust(d.getCurrentStateTrust()));

        // Variables — manifest-default when empty (mirrors Board.vue verify builder), then sort.
        sb.append("|vars[").append(variablesFingerprint(d.getVariables(), manifest)).append(']');
        // Privacies — manifest-default when empty, then sort.
        sb.append("|priv[").append(privaciesFingerprint(d.getPrivacies(), manifest)).append(']');
        return sb.toString();
    }

    private static String variablesFingerprint(List<VariableStateDto> variables, DeviceManifest manifest) {
        List<String> parts = new ArrayList<>();
        if (variables == null || variables.isEmpty()) {
            if (manifest != null && manifest.getInternalVariables() != null) {
                for (DeviceManifest.InternalVariable iv : manifest.getInternalVariables()) {
                    if (iv.getName() == null) continue;
                    // Frontend default: value = Default || '0' (no Default field exists), trust = 'trusted'.
                    parts.add(iv.getName() + "=" + normalizeValue("0") + "@" + normalizeTrust("trusted"));
                }
            }
        } else {
            for (VariableStateDto v : variables) {
                if (v == null || v.getName() == null) continue;
                parts.add(v.getName() + "=" + normalizeValue(v.getValue()) + "@" + normalizeTrust(v.getTrust()));
            }
        }
        parts.sort(String::compareTo);
        return String.join(",", parts);
    }

    private static String privaciesFingerprint(List<PrivacyStateDto> privacies, DeviceManifest manifest) {
        List<String> parts = new ArrayList<>();
        if (privacies == null || privacies.isEmpty()) {
            if (manifest != null && manifest.getInternalVariables() != null) {
                for (DeviceManifest.InternalVariable iv : manifest.getInternalVariables()) {
                    if (iv.getName() == null) continue;
                    // Frontend default: privacy = Privacy || 'public'.
                    String p = iv.getPrivacy() != null ? iv.getPrivacy() : "public";
                    parts.add(iv.getName() + "=" + normalizePrivacy(p));
                }
            }
        } else {
            for (PrivacyStateDto p : privacies) {
                if (p == null || p.getName() == null) continue;
                parts.add(p.getName() + "=" + normalizePrivacy(p.getPrivacy()));
            }
        }
        parts.sort(String::compareTo);
        return String.join(",", parts);
    }

    // ==================== specs ====================

    private static String specsFingerprint(List<SpecificationDto> specs,
                                           Map<String, DeviceSmvData> deviceSmvMap) {
        if (specs == null || specs.isEmpty()) return "";
        List<String> parts = new ArrayList<>();
        for (SpecificationDto s : specs) {
            if (s == null) continue;
            parts.add(specFingerprint(s, deviceSmvMap));
        }
        parts.sort(String::compareTo);
        return String.join(";", parts);
    }

    private static String specFingerprint(SpecificationDto s,
                                          Map<String, DeviceSmvData> deviceSmvMap) {
        StringBuilder sb = new StringBuilder();
        sb.append(nullSafe(s.getId()))
          .append('|').append(nullSafe(s.getTemplateId()))
          .append("|a(").append(conditionsFingerprint(s.getAConditions(), deviceSmvMap)).append(')')
          .append("|if(").append(conditionsFingerprint(s.getIfConditions(), deviceSmvMap)).append(')')
          .append("|then(").append(conditionsFingerprint(s.getThenConditions(), deviceSmvMap)).append(')');
        return sb.toString();
    }

    private static String conditionsFingerprint(List<SpecConditionDto> conditions,
                                                Map<String, DeviceSmvData> deviceSmvMap) {
        if (conditions == null || conditions.isEmpty()) return "";
        // Condition order within a side is not semantically load-bearing here, so sort for stability.
        List<String> parts = new ArrayList<>();
        for (SpecConditionDto c : conditions) {
            if (c == null) continue;
            String device = DeviceReferenceResolver.canonicalReference(
                    c.getDeviceId(), c.getDeviceLabel(), deviceSmvMap);
            parts.add(nullSafe(device)
                    + "#" + nullSafe(c.getTargetType())
                    + "#" + nullSafe(c.getKey())
                    + "#" + nullSafe(c.getRelation())
                    + "#" + normalizeValue(c.getValue()));
        }
        parts.sort(String::compareTo);
        return String.join(",", parts);
    }

    // ==================== helpers ====================

    /** Look up the manifest for a device from the built SMV map, trying normalized then raw varName. */
    private static DeviceManifest manifestFor(String normalizedVarName, String rawVarName,
                                              Map<String, DeviceSmvData> deviceSmvMap) {
        if (deviceSmvMap == null) return null;
        DeviceSmvData smv = deviceSmvMap.get(normalizedVarName);
        if (smv == null && rawVarName != null) smv = deviceSmvMap.get(rawVarName);
        return smv != null ? smv.getManifest() : null;
    }

    /**
     * Mirror of the frontend {@code normalizeValue}: strip surrounding quotes from a quoted number
     * (e.g. {@code "30"} → {@code 30}); leave everything else untouched. Idempotent, so applying it to
     * an already-stripped snapshot value is a no-op.
     */
    private static String normalizeValue(String value) {
        if (value == null || value.isEmpty()) return "";
        if (value.length() >= 2) {
            char first = value.charAt(0);
            char last = value.charAt(value.length() - 1);
            boolean quoted = (first == '"' && last == '"') || (first == '\'' && last == '\'');
            if (quoted) {
                String inner = value.substring(1, value.length() - 1);
                if (!inner.isEmpty() && inner.chars().allMatch(Character::isDigit)) {
                    return inner;
                }
            }
        }
        return value;
    }

    private static String normalizeTrust(String value) {
        String v = DeviceSmvDataFactory.normalizeTrustPrivacy(value);
        return v != null ? v : "trusted";
    }

    private static String normalizePrivacy(String value) {
        String v = DeviceSmvDataFactory.normalizeTrustPrivacy(value);
        return v != null ? v : "public";
    }

    private static String nullSafe(String value) {
        return value == null ? "" : value;
    }
}
