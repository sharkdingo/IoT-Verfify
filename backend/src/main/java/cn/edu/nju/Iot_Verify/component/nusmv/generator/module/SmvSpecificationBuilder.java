package cn.edu.nju.Iot_Verify.component.nusmv.generator.module;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

@Slf4j
@Component
public class SmvSpecificationBuilder {

    private static final String PERSISTENCE_TEMPLATE_ID = "6";
    private static final String CONDITION_SEPARATOR = " & ";

    public String build(java.util.List<SpecificationDto> specs, boolean isAttack, int intensity, 
                       Map<String, DeviceSmvData> deviceSmvMap) {
        StringBuilder content = new StringBuilder();
        
        if (specs == null || specs.isEmpty()) {
            log.debug("No specifications provided - skipping SPECIFICATION section");
            return content.toString();
        }
        
        content.append("\n-- Specifications\n");

        int generatedSpecs = 0;
        for (SpecificationDto spec : specs) {
            if (spec == null) continue;
            if ((spec.getAConditions() == null || spec.getAConditions().isEmpty()) &&
                (spec.getIfConditions() == null || spec.getIfConditions().isEmpty())) continue;

            String specString = generateSpecString(spec, isAttack, intensity, deviceSmvMap);
            content.append("\t").append(specString).append("\n");
            generatedSpecs++;
        }
        
        log.debug("Generated {} specifications", generatedSpecs);
        return content.toString();
    }

    /**
     * 生成单个规格字符串（需要传入 deviceSmvMap 以正确解析 trust/privacy 变量名）
     */
    public String generateSpecString(SpecificationDto spec, boolean isAttack, int intensity,
                                     Map<String, DeviceSmvData> deviceSmvMap) {
        String templateId = spec.getTemplateId();
        if (PERSISTENCE_TEMPLATE_ID.equals(templateId)) {
            return generateLtlSpec(spec, isAttack, intensity, deviceSmvMap);
        }
        return generateCtlSpec(spec, isAttack, intensity, deviceSmvMap);
    }

    private String generateLtlSpec(SpecificationDto spec, boolean isAttack, int intensity, 
                                  Map<String, DeviceSmvData> deviceSmvMap) {
        String ifPart = buildConditionGroup(spec.getIfConditions(), deviceSmvMap);
        String thenPart = buildConditionGroup(spec.getThenConditions(), deviceSmvMap);
        String antecedent = withAttackConstraint(ifPart, isAttack, intensity);

        return "LTLSPEC G((" + antecedent + ") -> F G(" + thenPart + "))";
    }

    private String generateCtlSpec(SpecificationDto spec, boolean isAttack, int intensity, 
                                  Map<String, DeviceSmvData> deviceSmvMap) {
        String templateId = spec.getTemplateId();
        String aPart = buildConditionGroup(spec.getAConditions(), deviceSmvMap);
        String ifPart = buildConditionGroup(spec.getIfConditions(), deviceSmvMap);
        String thenPart = buildConditionGroup(spec.getThenConditions(), deviceSmvMap);

        switch (templateId) {
            case "1": // always
                if (isTrueLiteral(aPart) && !isTrueLiteral(ifPart) && !isTrueLiteral(thenPart)) {
                    // aConditions 为空但有 if/then 条件时，生成 AG(if -> then)
                    return "CTLSPEC AG((" + withAttackConstraint(ifPart, isAttack, intensity) + ") -> (" + thenPart + "))";
                }
                return "CTLSPEC AG(" + withAttackConstraint(aPart, isAttack, intensity) + ")";
            case "2": // eventually
                return "CTLSPEC AF(" + withAttackConstraint(aPart, isAttack, intensity) + ")";
            case "3": // never
                return "CTLSPEC AG !(" + withAttackConstraint(aPart, isAttack, intensity) + ")";
            case "4": // immediate
                return "CTLSPEC AG((" + withAttackConstraint(ifPart, isAttack, intensity) + ") -> AX(" + thenPart + "))";
            case "5": // response
                return "CTLSPEC AG((" + withAttackConstraint(ifPart, isAttack, intensity) + ") -> AF(" + thenPart + "))";
            case "7": // safety: untrusted -> !A
                return buildSafetySpec(spec, deviceSmvMap, isAttack, intensity);
            default:
                return "CTLSPEC AG(" + withAttackConstraint(aPart, isAttack, intensity) + ")";
        }
    }

    private String genConditionSpec(SpecConditionDto cond, Map<String, DeviceSmvData> deviceSmvMap) {
        if (cond == null || cond.getDeviceId() == null) {
            log.warn("Invalid condition: deviceId is null");
            return "TRUE";
        }

        DeviceSmvData smv = deviceSmvMap != null ? DeviceSmvDataFactory.findDeviceSmvData(cond.getDeviceId(), deviceSmvMap) : null;
        String varName = smv != null ? smv.getVarName() : DeviceSmvDataFactory.toVarName(cond.getDeviceId());
        String targetType = cond.getTargetType();

        if ("api".equals(targetType)) {
            if (cond.getKey() == null) {
                log.warn("Condition key is null for api targetType");
                return "TRUE";
            }
            String apiSignal = DeviceSmvDataFactory.formatApiSignalName(cond.getKey());
            return varName + "." + apiSignal + "=TRUE";
        }

        if ("state".equals(targetType)) {
            return buildStateCondition(varName, smv, cond);
        }

        if ("variable".equals(targetType)) {
            return buildSimpleCondition(varName + "." + cond.getKey(), cond);
        }

        if ("trust".equals(targetType)) {
            String resolved = resolvePropertyKey(smv, cond.getKey(), "trust_");
            return buildSimpleCondition(varName + "." + resolved, cond);
        }

        if ("privacy".equals(targetType)) {
            String resolved = resolvePropertyKey(smv, cond.getKey(), "privacy_");
            return buildSimpleCondition(varName + "." + resolved, cond);
        }

        if (targetType == null) {
            // 默认当作 state 处理
            return buildStateCondition(varName, smv, cond);
        }
        return buildSimpleCondition(varName + "." + targetType, cond);
    }
    
    private String buildConditionGroup(List<SpecConditionDto> conditions, Map<String, DeviceSmvData> deviceSmvMap) {
        if (conditions == null || conditions.isEmpty()) {
            return "TRUE";
        }
        List<String> parts = new ArrayList<>();
        for (SpecConditionDto cond : conditions) {
            parts.add(genConditionSpec(cond, deviceSmvMap));
        }
        return String.join(CONDITION_SEPARATOR, parts);
    }

    private String buildStateCondition(String varName, DeviceSmvData smv, SpecConditionDto cond) {
        List<String> targets = resolveStateTargets(varName, smv, cond);
        String relation = normalizeRelation(cond.getRelation());
        String value = cond.getValue();
        if (relation == null || value == null) {
            log.warn("Condition relation or value is null for device: {}", cond.getDeviceId());
            return targets.isEmpty() ? "TRUE" : targets.get(0);
        }
        String normalizedValue = normalizeStateValueByRelation(relation, value);

        List<String> exprs = new ArrayList<>();
        for (String target : targets) {
            exprs.add(buildRelationExpr(target, relation, normalizedValue));
        }
        if (exprs.isEmpty()) {
            return "TRUE";
        }
        if (exprs.size() == 1) {
            return exprs.get(0);
        }
        return "(" + String.join(" | ", exprs) + ")";
    }

    private List<String> resolveStateTargets(String varName, DeviceSmvData smv, SpecConditionDto cond) {
        List<String> targets = new ArrayList<>();
        if (smv == null || smv.getModes() == null || smv.getModes().isEmpty()) {
            targets.add(varName + ".state");
            return targets;
        }

        // 单模式设备：直接使用模式名
        if (smv.getModes().size() == 1) {
            targets.add(varName + "." + smv.getModes().get(0));
            return targets;
        }

        String key = cond.getKey();
        if (key != null && smv.getModes().contains(key)) {
            targets.add(varName + "." + key);
            return targets;
        }

        String value = cond.getValue();
        String cleanValue = (value != null) ? DeviceSmvDataFactory.cleanStateName(value) : null;
        if (cleanValue != null) {
            for (String mode : smv.getModes()) {
                List<String> modeStates = smv.getModeStates().get(mode);
                if (modeStates != null && modeStates.contains(cleanValue)) {
                    targets.add(varName + "." + mode);
                }
            }
        }

        if (!targets.isEmpty()) {
            return targets;
        }

        for (String mode : smv.getModes()) {
            targets.add(varName + "." + mode);
        }
        return targets;
    }

    private String buildSimpleCondition(String left, SpecConditionDto cond) {
        if (left == null || left.contains("null")) {
            return "TRUE";
        }
        String relation = normalizeRelation(cond.getRelation());
        String value = cond.getValue();
        if (relation == null || value == null) {
            log.warn("Condition relation or value is null for device: {}", cond.getDeviceId());
            return left;
        }
        return buildRelationExpr(left, relation, value);
    }

    private String buildSafetySpec(SpecificationDto spec, Map<String, DeviceSmvData> deviceSmvMap,
                                   boolean isAttack, int intensity) {
        List<String> parts = new ArrayList<>();
        if (spec.getAConditions() != null) {
            for (SpecConditionDto cond : spec.getAConditions()) {
                String aExpr = genConditionSpec(cond, deviceSmvMap);
                String trustExpr = buildTrustForCondition(cond, deviceSmvMap);
                if (!isTrueLiteral(aExpr)) {
                    parts.add(aExpr);
                }
                if (trustExpr != null) {
                    parts.add(trustExpr + "=untrusted");
                }
                String attackExpr = buildAttackFalseForCondition(cond, deviceSmvMap);
                if (attackExpr != null) {
                    parts.add(attackExpr);
                }
            }
        }

        if (isAttack && intensity > 0) {
            parts.add("intensity<=" + intensity);
        }

        String body = parts.isEmpty() ? "TRUE" : String.join(CONDITION_SEPARATOR, parts);
        return "CTLSPEC AG !(" + body + ")";
    }

    private String buildTrustForCondition(SpecConditionDto cond, Map<String, DeviceSmvData> deviceSmvMap) {
        if (cond == null || cond.getDeviceId() == null) return null;
        DeviceSmvData smv = deviceSmvMap != null ? DeviceSmvDataFactory.findDeviceSmvData(cond.getDeviceId(), deviceSmvMap) : null;
        String varName = smv != null ? smv.getVarName() : DeviceSmvDataFactory.toVarName(cond.getDeviceId());

        if ("variable".equals(cond.getTargetType())) {
            return varName + ".trust_" + cond.getKey();
        }

        if ("state".equals(cond.getTargetType())) {
            return resolveStateTrust(varName, smv, cond);
        }

        if ("api".equals(cond.getTargetType())) {
            return resolveApiTrust(varName, smv, cond);
        }

        return null;
    }

    private String resolveStateTrust(String varName, DeviceSmvData smv, SpecConditionDto cond) {
        if (smv == null || smv.getModes() == null || smv.getModes().isEmpty()) {
            String stateVal = cond.getValue() != null ? cond.getValue() : cond.getKey();
            return varName + ".trust_" + DeviceSmvDataFactory.cleanStateName(stateVal);
        }

        if (smv.getModes().size() == 1) {
            String mode = smv.getModes().get(0);
            String stateVal = cond.getValue() != null ? cond.getValue() : cond.getKey();
            return varName + ".trust_" + mode + "_" + DeviceSmvDataFactory.cleanStateName(stateVal);
        }

        String value = cond.getValue();
        String cleanValue = (value != null) ? DeviceSmvDataFactory.cleanStateName(value) : null;
        if (cleanValue != null) {
            for (String mode : smv.getModes()) {
                List<String> modeStates = smv.getModeStates().get(mode);
                if (modeStates != null && modeStates.contains(cleanValue)) {
                    return varName + ".trust_" + mode + "_" + cleanValue;
                }
            }
        }

        String key = cond.getKey();
        if (key != null && smv.getModes().contains(key)) {
            if (cleanValue != null) {
                return varName + ".trust_" + key + "_" + cleanValue;
            }
            return varName + ".trust_" + key;
        }

        return null;
    }

    private String resolveApiTrust(String varName, DeviceSmvData smv, SpecConditionDto cond) {
        if (smv == null || smv.getManifest() == null || smv.getManifest().getApis() == null) {
            return null;
        }
        for (DeviceManifest.API api : smv.getManifest().getApis()) {
            if (api.getSignal() != null && api.getSignal() && api.getName().equals(cond.getKey())) {
                String endState = api.getEndState();
                if (endState == null) return null;
                if (smv.getModes() != null && !smv.getModes().isEmpty()) {
                    int modeIdx = DeviceSmvDataFactory.getModeIndexOfState(smv, endState);
                    if (modeIdx >= 0 && modeIdx < smv.getModes().size()) {
                        String mode = smv.getModes().get(modeIdx);
                        String cleanEndState = DeviceSmvDataFactory.cleanStateName(endState);
                        return varName + ".trust_" + mode + "_" + cleanEndState;
                    }
                }
                String cleanEndState = DeviceSmvDataFactory.cleanStateName(endState);
                return varName + ".trust_" + cleanEndState;
            }
        }
        return null;
    }

    /**
     * 解析 trust/privacy 条件的 key 为完整的 SMV 变量名。
     * key 可能是：
     * 1. 已包含 mode 前缀的完整名（如 "LockState_unlocked"）→ 直接使用
     * 2. 变量名（如 "temperature"）→ 直接使用
     * 3. 裸状态值（如 "unlocked"）→ 需要解析为 "Mode_value"
     */
    private String resolvePropertyKey(DeviceSmvData smv, String key, String prefix) {
        if (key == null) return prefix + "unknown";
        // 如果 key 已经包含下划线且匹配 mode 前缀，认为已经是完整名
        if (smv != null && smv.getModes() != null) {
            for (String mode : smv.getModes()) {
                if (key.startsWith(mode + "_")) {
                    return prefix + key;
                }
            }
        }
        // 检查是否是变量名
        if (smv != null && smv.getVariables() != null) {
            for (DeviceManifest.InternalVariable var : smv.getVariables()) {
                if (key.equals(var.getName())) {
                    return prefix + key;
                }
            }
        }
        // 尝试按状态值解析到 mode_state
        if (smv != null && smv.getModes() != null && smv.getModeStates() != null) {
            for (String mode : smv.getModes()) {
                List<String> states = smv.getModeStates().get(mode);
                if (states != null && states.contains(key.replace(" ", ""))) {
                    return prefix + mode + "_" + key.replace(" ", "");
                }
            }
            // 单模式设备 fallback
            if (smv.getModes().size() == 1) {
                return prefix + smv.getModes().get(0) + "_" + key.replace(" ", "");
            }
        }
        // 无法解析，原样返回
        return prefix + key;
    }

    private String buildAttackFalseForCondition(SpecConditionDto cond, Map<String, DeviceSmvData> deviceSmvMap) {
        if (cond == null || cond.getDeviceId() == null) return null;
        DeviceSmvData smv = deviceSmvMap != null ? DeviceSmvDataFactory.findDeviceSmvData(cond.getDeviceId(), deviceSmvMap) : null;
        String varName = smv != null ? smv.getVarName() : DeviceSmvDataFactory.toVarName(cond.getDeviceId());
        return varName + ".is_attack=FALSE";
    }

    private String buildRelationExpr(String left, String relation, String value) {
        if ("in".equals(relation) || "not_in".equals(relation) || "not in".equals(relation)) {
            List<String> values = splitValues(value);
            if (values.isEmpty()) {
                return "TRUE";
            }
            String op = "in".equals(relation) ? "=" : "!=";
            String join = "in".equals(relation) ? " | " : " & ";
            return "(" + values.stream()
                    .map(v -> left + op + v)
                    .collect(Collectors.joining(join)) + ")";
        }
        return left + relation + value;
    }

    private List<String> splitValues(String value) {
        if (value == null) return List.of();
        return Arrays.stream(value.split("[,;|]"))
                .map(String::trim)
                .filter(v -> !v.isEmpty())
                .collect(Collectors.toList());
    }

    private String normalizeStateValueByRelation(String relation, String value) {
        if (value == null) return null;
        if ("in".equals(relation) || "not_in".equals(relation) || "not in".equals(relation)) {
            return splitValues(value).stream()
                    .map(DeviceSmvDataFactory::cleanStateName)
                    .collect(Collectors.joining(","));
        }
        return DeviceSmvDataFactory.cleanStateName(value);
    }

    private String normalizeRelation(String relation) {
        if (relation == null) return null;
        if ("==".equals(relation)) return "=";
        if ("not_in".equals(relation)) return "not in";
        return relation;
    }

    private String withAttackConstraint(String condition, boolean isAttack, int intensity) {
        if (!isAttack || intensity <= 0) {
            return condition;
        }
        return "(" + condition + " & intensity<=" + intensity + ")";
    }

    private boolean isTrueLiteral(String s) {
        return s == null || s.trim().isEmpty() || "TRUE".equalsIgnoreCase(s.trim());
    }
}
