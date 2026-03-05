package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

/**
 * SMV 模型前置校验器（集中式）
 *
 * 在 SmvGenerator 生成 SMV 文本之前调用，提前发现模板/实例数据中的不合法项。
 * 所有硬性校验（会抛异常的）统一收口在此类，软性校验（仅 warn）也集中于此。
 */
@Slf4j
@Component
public class SmvModelValidator {

    /**
     * 执行全部校验。任何一项失败即抛出 SmvGenerationException。
     * 使用 IdentityHashMap 去重，确保同一 DeviceSmvData 对象只校验一次
     * （deviceSmvMap 中可能存在多个 key 指向同一对象的别名条目）。
     */
    public void validate(Map<String, DeviceSmvData> deviceSmvMap) {
        Set<DeviceSmvData> validated = Collections.newSetFromMap(new IdentityHashMap<>());
        for (DeviceSmvData smv : deviceSmvMap.values()) {
            if (smv.getManifest() == null) continue;
            if (!validated.add(smv)) continue;

            validateTriggerAttributes(smv);
            validateStartEndStates(smv);
            validateTrustPrivacyConsistency(smv);
            validatePropertyValues(smv);
        }
        validateEnvVarConflicts(deviceSmvMap);
    }

    /**
     * 软性校验：用户输入变量名是否存在于模板中（仅 warn，不抛异常）。
     * 从 DeviceSmvDataFactory 提取至此，由 Factory 调用。
     */
    public void warnUnknownUserVariables(DeviceSmvData smv, DeviceVerificationDto device) {
        if (device.getVariables() == null) return;
        Set<String> knownNames = new HashSet<>();
        for (DeviceManifest.InternalVariable v : smv.getVariables()) knownNames.add(v.getName());
        knownNames.addAll(smv.getEnvVariables().keySet());
        for (String mode : smv.getModes()) knownNames.add(mode);

        for (VariableStateDto var : device.getVariables()) {
            if (var.getName() != null && !knownNames.contains(var.getName())) {
                log.warn("Device '{}' (template '{}'): user-provided variable '{}' not found in template, ignored",
                        device.getVarName(), device.getTemplateName(), var.getName());
            }
        }
    }

    /**
     * 软性校验：无模式传感器设备传入 state 时警告。
     * 从 DeviceSmvDataFactory 提取至此，由 Factory 调用。
     */
    public void warnStatelessDeviceWithState(DeviceSmvData smv, DeviceVerificationDto device) {
        if (smv.getModes().isEmpty() && device.getState() != null && !device.getState().isBlank()) {
            log.warn("Device '{}' (template '{}') has no modes; user-provided state '{}' is ignored",
                    device.getVarName(), device.getTemplateName(), device.getState());
        }
    }

    // ==================== P1: Trigger.Attribute 合法性 ====================

    private void validateTriggerAttributes(DeviceSmvData smv) {
        DeviceManifest manifest = smv.getManifest();
        Set<String> legalAttrs = buildLegalAttributeSet(smv);

        if (manifest.getTransitions() != null) {
            for (DeviceManifest.Transition trans : manifest.getTransitions()) {
                String ctx = "Transition '" + trans.getName() + "'";
                // assignments 校验不依赖 trigger，始终执行
                validateAssignments(smv.getVarName(), ctx, trans.getAssignments());
                if (trans.getTrigger() == null) continue;
                validateTriggerCompleteness(smv.getVarName(), ctx, trans.getTrigger());
                String attr = trans.getTrigger().getAttribute();
                if (!legalAttrs.contains(attr)) {
                    throw SmvGenerationException.illegalTriggerAttribute(
                            smv.getVarName(), ctx, attr, legalAttrs);
                }
                validateTriggerRelation(smv.getVarName(), ctx, trans.getTrigger().getRelation());
            }
        }
        if (manifest.getApis() != null) {
            for (DeviceManifest.API api : manifest.getApis()) {
                String ctx = "API '" + api.getName() + "'";
                if (api.getTrigger() == null) continue;
                validateTriggerCompleteness(smv.getVarName(), ctx, api.getTrigger());
                String attr = api.getTrigger().getAttribute();
                if (!legalAttrs.contains(attr)) {
                    throw SmvGenerationException.illegalTriggerAttribute(
                            smv.getVarName(), ctx, attr, legalAttrs);
                }
                validateTriggerRelation(smv.getVarName(), ctx, api.getTrigger().getRelation());
            }
        }
    }

    private void validateTriggerCompleteness(String deviceName, String context, DeviceManifest.Trigger trigger) {
        if (trigger.getAttribute() == null || trigger.getAttribute().isBlank()) {
            throw SmvGenerationException.incompleteTrigger(deviceName, context, "attribute is null/blank");
        }
        if (trigger.getRelation() == null || trigger.getRelation().isBlank()) {
            throw SmvGenerationException.incompleteTrigger(deviceName, context, "relation is null/blank");
        }
        if (trigger.getValue() == null || trigger.getValue().isBlank()) {
            throw SmvGenerationException.incompleteTrigger(deviceName, context, "value is null/blank");
        }
    }

    private void validateTriggerRelation(String deviceName, String context, String rawRelation) {
        String normalized = normalizeTriggerRelation(rawRelation);
        if (!isSupportedTriggerRelation(normalized)) {
            throw SmvGenerationException.illegalTriggerRelation(
                    deviceName, context, rawRelation,
                    List.of("=", "!=", ">", ">=", "<", "<="));
        }
    }

    private String normalizeTriggerRelation(String relation) {
        return SmvRelationUtils.normalizeTriggerRelation(relation);
    }

    private boolean isSupportedTriggerRelation(String relation) {
        return SmvRelationUtils.isSupportedTriggerRelation(relation);
    }

    private void validateAssignments(String deviceName, String context, List<DeviceManifest.Assignment> assignments) {
        if (assignments == null) return;
        for (int i = 0; i < assignments.size(); i++) {
            DeviceManifest.Assignment a = assignments.get(i);
            if (a == null) {
                throw SmvGenerationException.incompleteTrigger(deviceName, context, "assignment[" + i + "] is null");
            }
            if (a.getAttribute() == null || a.getAttribute().isBlank()) {
                throw SmvGenerationException.incompleteTrigger(deviceName, context, "assignment[" + i + "].attribute is null/blank");
            }
            if (a.getValue() == null || a.getValue().isBlank()) {
                throw SmvGenerationException.incompleteTrigger(deviceName, context, "assignment[" + i + "].value is null/blank");
            }
        }
    }

    private Set<String> buildLegalAttributeSet(DeviceSmvData smv) {
        Set<String> attrs = new LinkedHashSet<>();
        attrs.addAll(smv.getModes());
        if (smv.getManifest().getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable iv : smv.getManifest().getInternalVariables()) {
                if (iv.getName() != null) attrs.add(iv.getName());
            }
        }
        return attrs;
    }

    // ==================== P2: StartState/EndState 格式与语义 ====================

    private void validateStartEndStates(DeviceSmvData smv) {
        DeviceManifest manifest = smv.getManifest();
        boolean multiMode = smv.getModes().size() > 1;
        int modeCount = smv.getModes().size();

        if (manifest.getApis() != null) {
            for (DeviceManifest.API api : manifest.getApis()) {
                validateStateString(smv, api.getName(), "API", api.getStartState(), multiMode, modeCount);
                validateStateString(smv, api.getName(), "API", api.getEndState(), multiMode, modeCount);
            }
        }
        if (manifest.getTransitions() != null) {
            for (DeviceManifest.Transition trans : manifest.getTransitions()) {
                validateStateString(smv, trans.getName(), "Transition", trans.getStartState(), multiMode, modeCount);
                validateStateString(smv, trans.getName(), "Transition", trans.getEndState(), multiMode, modeCount);
            }
        }
    }

    private void validateStateString(DeviceSmvData smv, String itemName, String itemType,
                                     String stateStr, boolean multiMode, int modeCount) {
        if (stateStr == null || stateStr.isBlank()) return;

        if (!multiMode) {
            if (stateStr.contains(";")) {
                throw SmvGenerationException.invalidStateFormat(smv.getVarName(), itemType, itemName, stateStr,
                        "contains ';' but device is single-mode");
            }
            if (!smv.getModes().isEmpty()) {
                String mode = smv.getModes().get(0);
                String clean = DeviceSmvDataFactory.cleanStateName(stateStr);
                List<String> legal = smv.getModeStates().get(mode);
                if (legal != null && !legal.isEmpty() && !clean.isEmpty() && !legal.contains(clean)) {
                    throw SmvGenerationException.invalidStateFormat(smv.getVarName(), itemType, itemName, clean,
                            "not in legal values " + legal + " for mode '" + mode + "'");
                }
            }
        } else {
            String[] parts = stateStr.split(";", -1);
            if (parts.length != modeCount) {
                throw SmvGenerationException.invalidStateFormat(smv.getVarName(), itemType, itemName, stateStr,
                        parts.length + " segments, expected " + modeCount + " (modes=" + smv.getModes() + ")");
            }
            for (int i = 0; i < parts.length; i++) {
                String rawSeg = parts[i].trim();
                if (rawSeg.isEmpty()) continue;
                String seg = DeviceSmvDataFactory.cleanStateName(rawSeg);
                String mode = smv.getModes().get(i);
                List<String> legal = smv.getModeStates().get(mode);
                if (legal != null && !legal.isEmpty() && !legal.contains(seg)) {
                    throw SmvGenerationException.invalidStateFormat(smv.getVarName(), itemType, itemName, stateStr,
                            "segment[" + i + "]='" + seg + "' not in legal values " + legal + " for mode '" + mode + "'");
                }
            }
        }
    }

    // ==================== P5: 同名 env var 冲突检测 ====================

    private void validateEnvVarConflicts(Map<String, DeviceSmvData> deviceSmvMap) {
        Map<String, List<EnvVarSource>> envSources = new LinkedHashMap<>();

        for (Map.Entry<String, DeviceSmvData> entry : deviceSmvMap.entrySet()) {
            DeviceSmvData smv = entry.getValue();
            if (smv.getManifest() == null) continue;
            if (!entry.getKey().equals(smv.getVarName())) continue;

            for (Map.Entry<String, DeviceManifest.InternalVariable> ev : smv.getEnvVariables().entrySet()) {
                envSources.computeIfAbsent(ev.getKey(), k -> new ArrayList<>())
                        .add(new EnvVarSource(smv.getVarName(), ev.getValue()));
            }
        }

        for (Map.Entry<String, List<EnvVarSource>> entry : envSources.entrySet()) {
            List<EnvVarSource> sources = entry.getValue();
            if (sources.size() <= 1) continue;
            EnvVarSource first = sources.get(0);
            for (int i = 1; i < sources.size(); i++) {
                checkEnvVarCompatibility(entry.getKey(), first, sources.get(i));
            }
        }
    }

    private void checkEnvVarCompatibility(String varName, EnvVarSource a, EnvVarSource b) {
        DeviceManifest.InternalVariable va = a.var;
        DeviceManifest.InternalVariable vb = b.var;

        boolean aIsEnum = va.getValues() != null && !va.getValues().isEmpty();
        boolean bIsEnum = vb.getValues() != null && !vb.getValues().isEmpty();
        boolean aIsNumeric = va.getLowerBound() != null && va.getUpperBound() != null;
        boolean bIsNumeric = vb.getLowerBound() != null && vb.getUpperBound() != null;

        if (aIsEnum != bIsEnum || aIsNumeric != bIsNumeric) {
            throw SmvGenerationException.envVarConflict(varName,
                    "type mismatch: device '" + a.device + "' declares " + describeType(va)
                            + ", device '" + b.device + "' declares " + describeType(vb));
        }
        if (aIsNumeric && (!Objects.equals(va.getLowerBound(), vb.getLowerBound())
                || !Objects.equals(va.getUpperBound(), vb.getUpperBound()))) {
            throw SmvGenerationException.envVarConflict(varName,
                    "range mismatch: device '" + a.device + "' declares " + va.getLowerBound() + ".." + va.getUpperBound()
                            + ", device '" + b.device + "' declares " + vb.getLowerBound() + ".." + vb.getUpperBound());
        }
        if (aIsEnum) {
            Set<String> setA = new TreeSet<>(va.getValues());
            Set<String> setB = new TreeSet<>(vb.getValues());
            if (!setA.equals(setB)) {
                throw SmvGenerationException.envVarConflict(varName,
                        "enum mismatch: device '" + a.device + "' declares " + setA
                                + ", device '" + b.device + "' declares " + setB);
            }
        }
    }

    private String describeType(DeviceManifest.InternalVariable v) {
        if (v.getValues() != null && !v.getValues().isEmpty()) return "enum" + v.getValues();
        if (v.getLowerBound() != null && v.getUpperBound() != null) return v.getLowerBound() + ".." + v.getUpperBound();
        return "boolean";
    }

    private static class EnvVarSource {
        final String device;
        final DeviceManifest.InternalVariable var;
        EnvVarSource(String device, DeviceManifest.InternalVariable var) {
            this.device = device;
            this.var = var;
        }
    }

    // ==================== P4: trust/privacy 值合法性 ====================

    private static final Set<String> VALID_TRUST_VALUES = Set.of("trusted", "untrusted");
    private static final Set<String> VALID_PRIVACY_VALUES = Set.of("public", "private");

    private static String normalize(String value) {
        return DeviceSmvDataFactory.normalizeTrustPrivacy(value);
    }

    private void validatePropertyValues(DeviceSmvData smv) {
        // modeStateTrust values
        for (Map.Entry<String, String> entry : smv.getModeStateTrust().entrySet()) {
            String val = entry.getValue();
            if (val != null && !VALID_TRUST_VALUES.contains(normalize(val))) {
                throw SmvGenerationException.smvGenerationError(
                        "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                + "': trust value '" + val + "' for key '" + entry.getKey()
                                + "' is invalid. Expected: " + VALID_TRUST_VALUES);
            }
        }
        // instanceStateTrust
        if (smv.getInstanceStateTrust() != null
                && !VALID_TRUST_VALUES.contains(normalize(smv.getInstanceStateTrust()))) {
            throw SmvGenerationException.smvGenerationError(
                    "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                            + "': instanceStateTrust '" + smv.getInstanceStateTrust()
                            + "' is invalid. Expected: " + VALID_TRUST_VALUES);
        }
        // instanceVariableTrust values
        for (Map.Entry<String, String> entry : smv.getInstanceVariableTrust().entrySet()) {
            String val = entry.getValue();
            if (val != null && !VALID_TRUST_VALUES.contains(normalize(val))) {
                throw SmvGenerationException.smvGenerationError(
                        "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                + "': variable trust '" + val + "' for '" + entry.getKey()
                                + "' is invalid. Expected: " + VALID_TRUST_VALUES);
            }
        }
        // instanceVariablePrivacy values
        for (Map.Entry<String, String> entry : smv.getInstanceVariablePrivacy().entrySet()) {
            String val = entry.getValue();
            if (val != null && !VALID_PRIVACY_VALUES.contains(normalize(val))) {
                throw SmvGenerationException.smvGenerationError(
                        "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                + "': privacy value '" + val + "' for '" + entry.getKey()
                                + "' is invalid. Expected: " + VALID_PRIVACY_VALUES);
            }
        }
        // content privacy values
        for (DeviceSmvData.ContentInfo ci : smv.getContents()) {
            if (ci.getPrivacy() != null && !VALID_PRIVACY_VALUES.contains(normalize(ci.getPrivacy()))) {
                throw SmvGenerationException.smvGenerationError(
                        "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                + "': content privacy '" + ci.getPrivacy() + "' for content '" + ci.getName()
                                + "' is invalid. Expected: " + VALID_PRIVACY_VALUES);
            }
        }
        // manifest variable trust values
        if (smv.getManifest() != null && smv.getManifest().getInternalVariables() != null) {
            for (DeviceManifest.InternalVariable var : smv.getManifest().getInternalVariables()) {
                if (var.getTrust() != null && !VALID_TRUST_VALUES.contains(normalize(var.getTrust()))) {
                    throw SmvGenerationException.smvGenerationError(
                            "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                    + "': manifest variable trust '" + var.getTrust() + "' for '" + var.getName()
                                    + "' is invalid. Expected: " + VALID_TRUST_VALUES);
                }
                if (var.getPrivacy() != null && !VALID_PRIVACY_VALUES.contains(normalize(var.getPrivacy()))) {
                    throw SmvGenerationException.smvGenerationError(
                            "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                    + "': manifest variable privacy '" + var.getPrivacy() + "' for '" + var.getName()
                                    + "' is invalid. Expected: " + VALID_PRIVACY_VALUES);
                }
            }
        }
        // manifest workingState privacy values
        if (smv.getManifest() != null && smv.getManifest().getWorkingStates() != null) {
            for (DeviceManifest.WorkingState ws : smv.getManifest().getWorkingStates()) {
                if (ws.getPrivacy() != null && !VALID_PRIVACY_VALUES.contains(normalize(ws.getPrivacy()))) {
                    throw SmvGenerationException.smvGenerationError(
                            "[INVALID_PROPERTY_VALUE] Device '" + smv.getVarName()
                                    + "': workingState privacy '" + ws.getPrivacy() + "' for state '" + ws.getName()
                                    + "' is invalid. Expected: " + VALID_PRIVACY_VALUES);
                }
            }
        }
    }

    // ==================== P3: trust/privacy 一致性校验 ====================

    private void validateTrustPrivacyConsistency(DeviceSmvData smv) {
        if (smv.isSensor()) return;
        DeviceManifest manifest = smv.getManifest();
        if (manifest.getWorkingStates() == null) return;

        Map<String, String> seenTrust = new HashMap<>();
        Map<String, String> seenPrivacy = new HashMap<>();

        for (DeviceManifest.WorkingState ws : manifest.getWorkingStates()) {
            if (ws.getName() == null) continue;
            if (smv.getModes().size() <= 1) {
                String key = (smv.getModes().isEmpty() ? "" : smv.getModes().get(0) + "_")
                        + DeviceSmvDataFactory.cleanStateName(ws.getName());
                checkConflict(seenTrust, key, ws.getTrust(), smv.getVarName(), "trust");
                checkConflict(seenPrivacy, key, ws.getPrivacy(), smv.getVarName(), "privacy");
            } else {
                String[] parts = ws.getName().split(";");
                for (int i = 0; i < parts.length && i < smv.getModes().size(); i++) {
                    String key = smv.getModes().get(i) + "_" + DeviceSmvDataFactory.cleanStateName(parts[i].trim());
                    checkConflict(seenTrust, key, ws.getTrust(), smv.getVarName(), "trust");
                    checkConflict(seenPrivacy, key, ws.getPrivacy(), smv.getVarName(), "privacy");
                }
            }
        }
    }

    private void checkConflict(Map<String, String> seen, String key, String value,
                               String varName, String dimension) {
        if (value == null) return;
        String normalized = normalize(value);
        String prev = seen.put(key, normalized);
        if (prev != null && !prev.equals(normalized)) {
            throw SmvGenerationException.trustPrivacyConflict(varName, key, prev, normalized);
        }
    }
}
