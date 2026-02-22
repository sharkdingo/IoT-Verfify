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

        content.append("\n-- Specifications");

        int generatedSpecs = 0;
        for (SpecificationDto spec : specs) {
            if (spec == null) continue;
            if ((spec.getAConditions() == null || spec.getAConditions().isEmpty()) &&
                (spec.getIfConditions() == null || spec.getIfConditions().isEmpty())) continue;

            try {
                String specString = generateSpecString(spec, isAttack, intensity, deviceSmvMap);
                content.append("\n\t").append(specString);
                generatedSpecs++;
            } catch (InvalidConditionException e) {
                // 无效条件导致 spec 无法生成，跳过并记录警告
                log.warn("Skipping spec '{}': {}", spec.getId(), e.getMessage());
                // 生成一个必定失败的 spec 占位，保持 spec 数量与 effectiveSpecs 一致
                String safeMsg = e.getMessage() != null ? e.getMessage().replaceAll("[\\r\\n]+", " ") : "unknown";
                content.append("\n\tCTLSPEC FALSE -- invalid spec: ").append(safeMsg);
                generatedSpecs++;
            }
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

        return "LTLSPEC G((" + ifPart + ") -> F G(" + thenPart + "))";
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
                    return "CTLSPEC AG((" + ifPart + ") -> (" + thenPart + "))";
                }
                return "CTLSPEC AG(" + aPart + ")";
            case "2": // eventually
                return "CTLSPEC AF(" + aPart + ")";
            case "3": // never
                return "CTLSPEC AG !(" + aPart + ")";
            case "4": // immediate
                return "CTLSPEC AG((" + ifPart + ") -> AX(" + thenPart + "))";
            case "5": // response
                return "CTLSPEC AG((" + ifPart + ") -> AF(" + thenPart + "))";
            case "7": // safety: untrusted -> !A
                return buildSafetySpec(spec, deviceSmvMap, isAttack, intensity);
            default:
                return "CTLSPEC AG(" + aPart + ")";
        }
    }

    private String genConditionSpec(SpecConditionDto cond, Map<String, DeviceSmvData> deviceSmvMap) {
        if (cond == null || cond.getDeviceId() == null) {
            throw new InvalidConditionException("condition deviceId is null");
        }

        DeviceSmvData smv = deviceSmvMap != null ? DeviceSmvDataFactory.findDeviceSmvData(cond.getDeviceId(), deviceSmvMap) : null;
        if (smv == null) {
            throw new InvalidConditionException("device '" + cond.getDeviceId() + "' not found in deviceSmvMap");
        }
        String varName = smv.getVarName();
        String targetType = cond.getTargetType() != null ? cond.getTargetType().toLowerCase() : null;

        if ("api".equals(targetType)) {
            if (cond.getKey() == null) {
                throw new InvalidConditionException("api condition key is null for device " + cond.getDeviceId());
            }
            String apiSignal = DeviceSmvDataFactory.formatApiSignalName(cond.getKey());
            if (apiSignal == null) {
                throw new InvalidConditionException("api signal name resolved to null for key '" + cond.getKey() + "' on device " + cond.getDeviceId());
            }
            // 校验 API 存在且为 signal 类型
            validateApiSignalExists(smv, cond.getKey(), cond.getDeviceId());
            // API 信号为布尔变量，仅允许 =, !=, IN, NOT_IN
            validateApiBooleanRelation(cond);
            return buildSimpleCondition(varName + "." + apiSignal, cond);
        }

        if ("state".equals(targetType)) {
            return buildStateCondition(varName, smv, cond);
        }

        if ("variable".equals(targetType)) {
            return buildVariableCondition(varName, smv, cond);
        }

        if ("trust".equals(targetType)) {
            String resolved = resolvePropertyKey(smv, cond.getKey(), "trust_", cond.getDeviceId());
            return buildSimpleCondition(varName + "." + resolved, cond);
        }

        if ("privacy".equals(targetType)) {
            String resolved = resolvePropertyKey(smv, cond.getKey(), "privacy_", cond.getDeviceId());
            return buildSimpleCondition(varName + "." + resolved, cond);
        }

        // 未知 targetType → fail-closed，不再猜测拼接
        throw new InvalidConditionException("unsupported targetType '" + targetType
                + "' for device " + cond.getDeviceId() + "; allowed: state, variable, api, trust, privacy");
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
        if (relation == null) {
            throw new InvalidConditionException("state condition relation is null for device " + cond.getDeviceId());
        }
        if (!isSupportedRelation(relation)) {
            throw new InvalidConditionException("unsupported relation '" + cond.getRelation()
                    + "' for state condition on device " + cond.getDeviceId());
        }
        if (value == null || value.isBlank()) {
            throw new InvalidConditionException("state condition value is null/blank for device " + cond.getDeviceId());
        }
        String normalizedValue = normalizeStateValueByRelation(relation, value);
        if (normalizedValue == null || normalizedValue.isBlank()) {
            throw new InvalidConditionException("state condition value is blank after normalization for device " + cond.getDeviceId());
        }

        List<String> exprs = new ArrayList<>();
        for (String target : targets) {
            exprs.add(buildRelationExpr(target, relation, normalizedValue));
        }
        if (exprs.isEmpty()) {
            throw new InvalidConditionException("no state targets resolved for device " + cond.getDeviceId());
        }
        if (exprs.size() == 1) {
            return exprs.get(0);
        }
        return "(" + String.join(" | ", exprs) + ")";
    }

    private List<String> resolveStateTargets(String varName, DeviceSmvData smv, SpecConditionDto cond) {
        List<String> targets = new ArrayList<>();
        if (smv == null || smv.getModes() == null || smv.getModes().isEmpty()) {
            // 无 mode 设备（纯传感器）不声明 state 变量，无法生成 state 条件
            throw new InvalidConditionException("device '" + varName + "' has no modes, cannot generate state condition");
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
        // IN/NOT_IN: 拆分值列表，逐个检查属于哪个 mode
        String relation = normalizeRelation(cond.getRelation());
        List<String> valueParts = ("in".equals(relation) || "not in".equals(relation))
                ? splitValues(value) : (value != null ? List.of(value) : List.of());
        for (String singleVal : valueParts) {
            String cleanValue = DeviceSmvDataFactory.cleanStateName(singleVal);
            for (String mode : smv.getModes()) {
                List<String> modeStates = smv.getModeStates().get(mode);
                if (modeStates != null && modeStates.contains(cleanValue)) {
                    String target = varName + "." + mode;
                    if (!targets.contains(target)) {
                        targets.add(target);
                    }
                }
            }
        }

        if (!targets.isEmpty()) {
            return targets;
        }

        // 无法确定值属于哪个 mode，fail-closed 而非猜测所有 mode
        throw new InvalidConditionException("multi-mode device '" + varName
                + "': value '" + value + "' not found in any mode's state list");
    }

    private String buildSimpleCondition(String left, SpecConditionDto cond) {
        if (left == null || left.contains("null")) {
            throw new InvalidConditionException("invalid left-hand side: " + left);
        }
        String relation = normalizeRelation(cond.getRelation());
        String value = cond.getValue();
        if (relation == null) {
            throw new InvalidConditionException("simple condition relation is null for device " + cond.getDeviceId());
        }
        if (!isSupportedRelation(relation)) {
            throw new InvalidConditionException("unsupported relation '" + cond.getRelation()
                    + "' for device " + cond.getDeviceId());
        }
        if (value == null || value.isBlank()) {
            throw new InvalidConditionException("simple condition value is null/blank for device " + cond.getDeviceId());
        }
        return buildRelationExpr(left, relation, value);
    }

    private String buildVariableCondition(String varName, DeviceSmvData smv, SpecConditionDto cond) {
        String key = cond.getKey();
        if (key == null || key.isBlank()) {
            throw new InvalidConditionException("variable condition key is null/blank for device " + cond.getDeviceId());
        }
        String normalizedKey = key.trim();

        if (normalizedKey.startsWith("a_")) {
            String envName = normalizedKey.substring(2);
            if (smv.getEnvVariables() != null && smv.getEnvVariables().containsKey(envName)) {
                return buildSimpleCondition("a_" + envName, cond);
            }
            throw new InvalidConditionException("env variable '" + normalizedKey + "' not found on device " + cond.getDeviceId());
        }

        if (smv.getEnvVariables() != null && smv.getEnvVariables().containsKey(normalizedKey)) {
            return buildSimpleCondition("a_" + normalizedKey, cond);
        }

        if (hasInternalVariable(smv, normalizedKey)) {
            return buildSimpleCondition(varName + "." + normalizedKey, cond);
        }

        throw new InvalidConditionException("variable key '" + normalizedKey + "' not found as internal/env variable on device "
                + cond.getDeviceId());
    }

    private boolean hasInternalVariable(DeviceSmvData smv, String name) {
        if (smv == null || smv.getVariables() == null || name == null) return false;
        for (DeviceManifest.InternalVariable var : smv.getVariables()) {
            if (var != null && name.equals(var.getName())) {
                return true;
            }
        }
        return false;
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
                // is_attack 变量仅在攻击模式下声明，非攻击模式引用会导致 NuSMV undefined variable 错误
                if (isAttack) {
                    String attackExpr = buildAttackFalseForCondition(cond, deviceSmvMap);
                    if (attackExpr != null) {
                        parts.add(attackExpr);
                    }
                }
            }
        }

        // intensity 约束已由 main module 的 INVAR 全局控制，不再注入到 safety spec

        String body = parts.isEmpty() ? "TRUE" : String.join(CONDITION_SEPARATOR, parts);
        return "CTLSPEC AG !(" + body + ")";
    }

    private String buildTrustForCondition(SpecConditionDto cond, Map<String, DeviceSmvData> deviceSmvMap) {
        if (cond == null || cond.getDeviceId() == null) return null;
        DeviceSmvData smv = deviceSmvMap != null ? DeviceSmvDataFactory.findDeviceSmvData(cond.getDeviceId(), deviceSmvMap) : null;
        String varName = smv != null ? smv.getVarName() : DeviceSmvDataFactory.toVarName(cond.getDeviceId());
        String targetType = cond.getTargetType() != null ? cond.getTargetType().toLowerCase() : null;

        if ("variable".equals(targetType)) {
            if (cond.getKey() == null || cond.getKey().isBlank()) {
                return null;
            }
            String normalizedKey = cond.getKey().trim();
            if (normalizedKey.startsWith("a_")) {
                normalizedKey = normalizedKey.substring(2);
            }
            if (smv != null) {
                boolean exists = (smv.getEnvVariables() != null && smv.getEnvVariables().containsKey(normalizedKey))
                        || hasInternalVariable(smv, normalizedKey);
                if (!exists) {
                    return null;
                }
            }
            return varName + ".trust_" + normalizedKey;
        }

        if ("state".equals(targetType)) {
            return resolveStateTrust(varName, smv, cond);
        }

        if ("api".equals(targetType)) {
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
                        String[] endParts = endState.split(";");
                        String cleanEndState = (modeIdx < endParts.length)
                                ? endParts[modeIdx].trim().replace(" ", "")
                                : DeviceSmvDataFactory.cleanStateName(endState);
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
    private String resolvePropertyKey(DeviceSmvData smv, String key, String prefix, String deviceId) {
        if (smv == null) {
            throw new InvalidConditionException("device '" + deviceId + "' not found when resolving property key");
        }
        if (key == null || key.isBlank()) {
            throw new InvalidConditionException("property key is null/blank for device " + deviceId);
        }

        String normalizedKey = key.trim();
        if (normalizedKey.startsWith(prefix)) {
            normalizedKey = normalizedKey.substring(prefix.length());
        }
        String cleanKey = normalizedKey.replace(" ", "");

        // 1) 完整 mode_state
        if (smv.getModes() != null && smv.getModeStates() != null) {
            for (String mode : smv.getModes()) {
                String modePrefix = mode + "_";
                if (cleanKey.startsWith(modePrefix)) {
                    String stateName = cleanKey.substring(modePrefix.length());
                    List<String> states = smv.getModeStates().get(mode);
                    if (states != null && states.contains(stateName)) {
                        return prefix + mode + "_" + stateName;
                    }
                    throw new InvalidConditionException("property key '" + key + "' references unknown state '" + stateName
                            + "' in mode '" + mode + "' for device " + deviceId);
                }
            }
        }

        // 2) 变量名
        if (hasInternalVariable(smv, cleanKey)) {
            return prefix + cleanKey;
        }

        // 3) 裸状态值 -> 解析为 mode_state
        if (smv.getModes() != null && smv.getModeStates() != null) {
            List<String> matchedModes = new ArrayList<>();
            for (String mode : smv.getModes()) {
                List<String> states = smv.getModeStates().get(mode);
                if (states != null && states.contains(cleanKey)) {
                    matchedModes.add(mode);
                }
            }
            if (matchedModes.size() == 1) {
                return prefix + matchedModes.get(0) + "_" + cleanKey;
            }
            if (matchedModes.size() > 1) {
                throw new InvalidConditionException("property key '" + key + "' is ambiguous across modes "
                        + matchedModes + " on device " + deviceId);
            }
            if (smv.getModes().size() == 1) {
                String onlyMode = smv.getModes().get(0);
                List<String> states = smv.getModeStates().get(onlyMode);
                if (states != null && states.contains(cleanKey)) {
                    return prefix + onlyMode + "_" + cleanKey;
                }
            }
        }

        throw new InvalidConditionException("cannot resolve property key '" + key + "' for device " + deviceId);
    }

    private String buildAttackFalseForCondition(SpecConditionDto cond, Map<String, DeviceSmvData> deviceSmvMap) {
        if (cond == null || cond.getDeviceId() == null) return null;
        DeviceSmvData smv = deviceSmvMap != null ? DeviceSmvDataFactory.findDeviceSmvData(cond.getDeviceId(), deviceSmvMap) : null;
        String varName = smv != null ? smv.getVarName() : DeviceSmvDataFactory.toVarName(cond.getDeviceId());
        return varName + ".is_attack=FALSE";
    }

    private void validateApiSignalExists(DeviceSmvData smv, String apiKey, String deviceId) {
        if (smv.getManifest() == null || smv.getManifest().getApis() == null) {
            throw new InvalidConditionException("device '" + deviceId + "' has no APIs defined");
        }
        for (DeviceManifest.API api : smv.getManifest().getApis()) {
            if (api.getName() != null && api.getName().equals(apiKey)
                    && api.getSignal() != null && api.getSignal()) {
                return;
            }
        }
        throw new InvalidConditionException("api '" + apiKey + "' not found or not a signal on device '" + deviceId + "'");
    }

    private static final List<String> API_ALLOWED_NORMALIZED_RELATIONS = List.of("=", "!=", "in", "not in");

    private void validateApiBooleanRelation(SpecConditionDto cond) {
        String rel = cond.getRelation();
        String normalized = normalizeRelation(rel);
        if (normalized == null || !API_ALLOWED_NORMALIZED_RELATIONS.contains(normalized)) {
            throw new InvalidConditionException("api condition only supports =, !=, IN, NOT_IN relations, got '"
                    + rel + "' for device " + cond.getDeviceId());
        }
        // 值必须为布尔字面量（TRUE/FALSE），或 IN/NOT_IN 的逗号分隔布尔列表
        String value = cond.getValue();
        if (value != null) {
            if ("in".equals(normalized) || "not in".equals(normalized)) {
                for (String v : splitValues(value)) {
                    if (!"TRUE".equalsIgnoreCase(v) && !"FALSE".equalsIgnoreCase(v)) {
                        throw new InvalidConditionException("api condition value must be TRUE or FALSE, got '" + v
                                + "' for device " + cond.getDeviceId());
                    }
                }
            } else if (!"TRUE".equalsIgnoreCase(value.trim()) && !"FALSE".equalsIgnoreCase(value.trim())) {
                throw new InvalidConditionException("api condition value must be TRUE or FALSE, got '" + value
                        + "' for device " + cond.getDeviceId());
            }
        }
    }

    private String buildRelationExpr(String left, String relation, String value) {
        if ("in".equals(relation) || "not in".equals(relation)) {
            List<String> values = splitValues(value);
            if (values.isEmpty()) {
                throw new InvalidConditionException("empty value list for '" + relation + "' relation on " + left);
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
        if ("in".equals(relation) || "not in".equals(relation)) {
            return splitValues(value).stream()
                    .map(DeviceSmvDataFactory::cleanStateName)
                    .collect(Collectors.joining(","));
        }
        return DeviceSmvDataFactory.cleanStateName(value);
    }

    private String normalizeRelation(String relation) {
        if (relation == null) return null;
        String normalized = relation.trim();
        return switch (normalized.toUpperCase()) {
            case "EQ", "==" -> "=";
            case "NEQ", "!=" -> "!=";
            case "GT" -> ">";
            case "GTE" -> ">=";
            case "LT" -> "<";
            case "LTE" -> "<=";
            case "IN" -> "in";
            case "NOT_IN", "NOT IN" -> "not in";
            default -> normalized;
        };
    }

    private boolean isSupportedRelation(String relation) {
        return "=".equals(relation)
                || "!=".equals(relation)
                || ">".equals(relation)
                || ">=".equals(relation)
                || "<".equals(relation)
                || "<=".equals(relation)
                || "in".equals(relation)
                || "not in".equals(relation);
    }

    private boolean isTrueLiteral(String s) {
        return s == null || s.trim().isEmpty() || "TRUE".equalsIgnoreCase(s.trim());
    }

    /** 标记无效条件数据导致 spec 无法正确生成 */
    static class InvalidConditionException extends RuntimeException {
        InvalidConditionException(String message) {
            super(message);
        }
    }
}
