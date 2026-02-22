package cn.edu.nju.Iot_Verify.component.nusmv.generator.module;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.PropertyDimension;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

@Slf4j
@Component
public class SmvMainModuleBuilder {

    public String build(Long userId,
                       List<DeviceVerificationDto> devices,
                       List<RuleDto> rules,
                       Map<String, DeviceSmvData> deviceSmvMap,
                       boolean isAttack,
                       int intensity,
                       boolean enablePrivacy) {

        // 参数验证
        if (devices == null) {
            log.error("SmvMainModuleBuilder.build: devices 参数不能为 null");
            throw new IllegalArgumentException("devices 参数不能为 null");
        }
        if (deviceSmvMap == null) {
            log.error("SmvMainModuleBuilder.build: deviceSmvMap 参数不能为 null");
            throw new IllegalArgumentException("deviceSmvMap 参数不能为 null");
        }

        StringBuilder content = new StringBuilder();

        content.append("\nMODULE main");

        // intensity 是冻结变量（与 MEDIC 一致）：值由各设备 is_attack 之和决定，验证过程中不变
        // 只要 isAttack=true 就声明 intensity，并用 INVAR 约束上限
        // intensity=0 时 INVAR intensity<=0 强制所有 is_attack=FALSE，语义闭合
        if (isAttack) {
            content.append("\nFROZENVAR");
            content.append("\n\tintensity: 0..50;");
            content.append("\nINVAR intensity <= ").append(intensity).append(";");
        }

        content.append("\nVAR");

        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null) continue;

            String moduleName = smv.getModuleName();
            String varName = smv.getVarName();
            content.append("\n\t").append(varName).append(": ").append(moduleName).append(";");
        }

        Set<String> declaredEnvVars = new HashSet<>();
        // 收集环境变量的用户初始值来源（varName -> deviceVarName -> validatedInit）
        Map<String, Map<String, String>> envVarInitSources = new LinkedHashMap<>();
        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.getEnvVariables() == null) continue;

            for (String varName : smv.getEnvVariables().keySet()) {
                DeviceManifest.InternalVariable var = smv.getEnvVariables().get(varName);
                if (var == null) {
                    continue;
                }
                if (!declaredEnvVars.contains(varName)) {
                    declaredEnvVars.add(varName);
                    content.append("\n\ta_").append(varName).append(": ");
                    if (var.getValues() != null && !var.getValues().isEmpty()) {
                        List<String> cleanValues = new ArrayList<>();
                        for (String v : var.getValues()) {
                            cleanValues.add(v.replace(" ", ""));
                        }
                        content.append("{").append(String.join(", ", cleanValues)).append("};");
                    } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                        int lower = var.getLowerBound();
                        int upper = var.getUpperBound();
                        // 攻击模式下扩大环境变量范围，模拟传感器数据篡改
                        // 扩展量与 intensity 成正比
                        if (isAttack) {
                            int range = upper - lower;
                            int expansion = (int)(range / 5.0 * intensity / 50.0);
                            upper = upper + expansion;
                        }
                        content.append(lower).append("..").append(upper).append(";");
                    } else {
                        // NuSMV has no "integer" type; use a safe default range
                        content.append("0..100;");
                    }
                }
                // 记录每个设备提供的初始值（校验范围），用于检测同名 env var 的冲突输入
                String userInit = smv.getVariableValues().get(varName);
                if (userInit != null && !userInit.isBlank()) {
                    String validatedInit = validateEnvVarInitValue(varName, userInit, var, isAttack, intensity);
                    if (validatedInit != null) {
                        envVarInitSources
                                .computeIfAbsent(varName, k -> new LinkedHashMap<>())
                                .put(smv.getVarName(), validatedInit);
                    }
                }
            }
        }

        Map<String, String> envVarInitValues = resolveEnvVarInitValues(envVarInitSources);

        content.append("\nASSIGN");

        // 生成环境变量的 init()（使用用户指定的初始值）
        for (Map.Entry<String, String> entry : envVarInitValues.entrySet()) {
            content.append("\n\tinit(a_").append(entry.getKey()).append(") := ")
                   .append(entry.getValue()).append(";");
        }

        if (isAttack) {
            content.append("\n\tinit(intensity) := 0");
            for (DeviceVerificationDto device : devices) {
                DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
                if (smv != null) {
                    String varName = smv.getVarName();
                    content.append(" + toint(").append(varName).append(".is_attack)");
                }
            }
            content.append(";");
        }

        appendStateTransitions(content, devices, rules, deviceSmvMap, isAttack);
        appendEnvTransitions(content, devices, deviceSmvMap);
        appendApiSignalTransitions(content, devices, deviceSmvMap);
        appendTransitionSignalTransitions(content, devices, deviceSmvMap);
        appendPropertyTransitions(content, devices, rules, deviceSmvMap, isAttack, PropertyDimension.TRUST);
        if (enablePrivacy) {
            appendPropertyTransitions(content, devices, rules, deviceSmvMap, isAttack, PropertyDimension.PRIVACY);
        }
        appendVariablePropertyTransitions(content, devices, deviceSmvMap, PropertyDimension.TRUST);
        if (enablePrivacy) {
            appendVariablePropertyTransitions(content, devices, deviceSmvMap, PropertyDimension.PRIVACY);
            appendContentPrivacyTransitions(content, devices, rules, deviceSmvMap);
        }
        appendVariableRateTransitions(content, devices, deviceSmvMap);
        appendExternalVariableAssignments(content, devices, deviceSmvMap);
        appendInternalVariableTransitions(content, devices, deviceSmvMap, isAttack);

        return content.toString();
    }

    /**
     * 为所有设备的 IsInside=false 变量生成简单赋值（镜像环境变量）。
     * 例如：thermostat.temperature := a_temperature;
     * 不限于传感器设备——非传感器设备（如 Thermostat）的外部变量也需要连接到环境变量。
     */
    private void appendExternalVariableAssignments(StringBuilder content,
                                                   List<DeviceVerificationDto> devices,
                                                   Map<String, DeviceSmvData> deviceSmvMap) {
        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.getManifest() == null) continue;

            String varName = smv.getVarName();

            if (smv.getManifest().getInternalVariables() != null) {
                for (DeviceManifest.InternalVariable var : smv.getManifest().getInternalVariables()) {
                    if (var.getIsInside() != null && !var.getIsInside()) {
                        content.append("\n\t").append(varName).append(".").append(var.getName())
                               .append(" := a_").append(var.getName()).append(";");
                    }
                }
            }
        }
    }

    private void appendStateTransitions(StringBuilder content,
                                       List<DeviceVerificationDto> devices,
                                       List<RuleDto> rules,
                                       Map<String, DeviceSmvData> deviceSmvMap,
                                       boolean isAttack) {
        
        Map<String, List<RuleDto>> rulesByTarget = new LinkedHashMap<>();
        if (rules != null) {
            for (RuleDto rule : rules) {
                if (rule == null || rule.getCommand() == null) continue;
                String targetDevice = rule.getCommand().getDeviceName();
                rulesByTarget.computeIfAbsent(targetDevice, k -> new ArrayList<>()).add(rule);
            }
        }

        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.getModes() == null) continue;

            String varName = smv.getVarName();
            List<RuleDto> deviceRules = rulesByTarget.get(device.getVarName());
            if (deviceRules == null) {
                deviceRules = rulesByTarget.get(smv.getTemplateName());
            }

            if (!smv.getModes().isEmpty()) {
                for (int modeIdx = 0; modeIdx < smv.getModes().size(); modeIdx++) {
                    String mode = smv.getModes().get(modeIdx);
                    List<String> modeStates = smv.getModeStates().get(mode);
                    if (modeStates == null || modeStates.isEmpty()) continue;

                    content.append("\n\tnext(").append(varName).append(".").append(mode).append(") :=\n");
                    content.append("\tcase\n");

                    if (deviceRules != null) {
                        for (RuleDto rule : deviceRules) {
                            if (rule.getCommand() == null || rule.getCommand().getAction() == null) {
                                continue;
                            }
                            String action = rule.getCommand().getAction();

                            DeviceManifest.API matchedApi = DeviceSmvDataFactory.findApi(smv.getManifest(), action);
                            if (matchedApi == null) continue;

                            String endState = getStateForMode(matchedApi.getEndState(), modeIdx);
                            if (endState == null || endState.isEmpty()) continue;

                            String startState = getStateForMode(matchedApi.getStartState(), modeIdx);

                            content.append("\t\t");
                            appendRuleConditions(content, rule, deviceSmvMap);

                            if (startState != null && !startState.isEmpty()) {
                                content.append(" & ").append(varName).append(".").append(mode).append("=").append(startState);
                            }

                            if (isAttack) {
                                content.append(" & ").append(varName).append(".is_attack=FALSE");
                            }

                            content.append(": ").append(endState).append(";\n");
                        }
                    }

                    if (smv.getManifest() != null && smv.getManifest().getTransitions() != null) {
                        for (DeviceManifest.Transition trans : smv.getManifest().getTransitions()) {
                            if (trans.getEndState() == null) continue;
                            String endState = getStateForMode(trans.getEndState(), modeIdx);
                            if (endState == null || endState.isEmpty()) continue;

                            DeviceManifest.Trigger trigger = trans.getTrigger();
                            if (trigger != null) {
                                // M4 修复：trigger value 需要去空格
                                String triggerValue = trigger.getValue() != null ? trigger.getValue().replace(" ", "") : "";
                                String startState = getStateForMode(trans.getStartState(), modeIdx);

                                content.append("\t\t");
                                if (startState != null && !startState.isEmpty()) {
                                    content.append(varName).append(".").append(mode).append("=").append(startState).append(" & ");
                                }
                                content.append(varName).append(".")
                                       .append(trigger.getAttribute())
                                       .append(trigger.getRelation())
                                       .append(triggerValue).append(": ").append(endState).append(";\n");
                            }
                        }
                    }

                    content.append("\t\tTRUE: ").append(varName).append(".").append(mode).append(";\n");
                    content.append("\tesac;");
                }
            }
        }
    }

    private void appendRuleConditions(StringBuilder content, RuleDto rule, Map<String, DeviceSmvData> deviceSmvMap) {
        if (rule.getConditions() == null || rule.getConditions().isEmpty()) {
            content.append("TRUE");
            return;
        }

        List<String> parts = new ArrayList<>();
        for (RuleDto.Condition condition : rule.getConditions()) {
            if (condition == null) {
                // fail-closed: malformed condition entry disables this rule
                log.warn("Rule contains a null condition entry - rule will never fire");
                content.append("FALSE");
                return;
            }

            String part = buildSingleCondition(condition, deviceSmvMap);
            if (part != null && !part.isEmpty()) {
                parts.add(part);
            } else {
                // fail-closed: unresolved condition disables this rule
                log.warn("Rule condition on device '{}' attribute '{}' could not be resolved - rule will never fire",
                        condition.getDeviceName(), condition.getAttribute());
                content.append("FALSE");
                return;
            }
        }

        if (parts.isEmpty()) {
            // fail-closed: non-empty input but no resolvable condition
            log.warn("Rule has non-empty condition list but no resolvable condition - rule will never fire");
            content.append("FALSE");
        } else {
            content.append(String.join(" & ", parts));
        }
    }

    private String buildSingleCondition(RuleDto.Condition condition, Map<String, DeviceSmvData> deviceSmvMap) {
        String deviceId = condition.getDeviceName();
        DeviceSmvData condSmv = DeviceSmvDataFactory.findDeviceSmvData(deviceId, deviceSmvMap);

        if (condSmv == null) {
            log.warn("Rule condition references unknown device '{}' and cannot be resolved", deviceId);
            return null;
        }

        String varName = condSmv.getVarName();
        String attr = condition.getAttribute();
        if (attr == null || attr.isBlank()) {
            log.warn("Rule condition has null/blank attribute for device '{}' and cannot be resolved", deviceId);
            return null;
        }

        if (condition.getRelation() != null) {
            // relation 非空时 value 也必须非空，否则无法生成有效条件
            if (condition.getValue() == null || condition.getValue().isBlank()) {
                log.warn("Rule condition has relation '{}' but null/blank value for device '{}' and cannot be resolved",
                        condition.getRelation(), deviceId);
                return null;
            }
            // M1/M2: 当 attribute="state" 时，解析为实际的 mode 变量名
            String normalizedRel = normalizeRuleRelation(condition.getRelation());
            if (!isSupportedRuleRelation(normalizedRel)) {
                log.warn("Rule condition has unsupported relation '{}' (normalized '{}') for device '{}'",
                        condition.getRelation(), normalizedRel, deviceId);
                return null;
            }
            if (("in".equals(normalizedRel) || "not in".equals(normalizedRel))
                    && splitRuleValues(condition.getValue()).isEmpty()) {
                log.warn("Rule condition has empty value list for '{}' relation on device '{}'",
                        normalizedRel, deviceId);
                return null;
            }
            if ("state".equals(attr) && condSmv.getModes() != null && !condSmv.getModes().isEmpty()) {
                String value = condition.getValue();
                // IN/NOT_IN: 拆分值列表，逐个匹配 mode state
                List<String> valueParts = splitRuleValues(value);
                List<String> matchedExprs = new ArrayList<>();
                boolean hasUnresolvedValue = false;
                for (String singleVal : valueParts) {
                    String cleanValue = DeviceSmvDataFactory.cleanStateName(singleVal);
                    boolean matchedCurrentValue = false;
                    for (String mode : condSmv.getModes()) {
                        List<String> modeStateList = condSmv.getModeStates().get(mode);
                        if (modeStateList != null) {
                            for (String ms : modeStateList) {
                                String suffix = ms.startsWith(mode + "_") ? ms.substring(mode.length() + 1) : ms;
                                if (suffix.equals(cleanValue) || ms.equals(cleanValue)) {
                                    matchedCurrentValue = true;
                                    // 对于 IN/NOT_IN，每个值单独用 = 或 != 匹配
                                    if ("in".equals(normalizedRel)) {
                                        matchedExprs.add(varName + "." + mode + "=" + ms);
                                    } else if ("not in".equals(normalizedRel)) {
                                        matchedExprs.add(varName + "." + mode + "!=" + ms);
                                    } else {
                                        matchedExprs.add(varName + "." + mode + normalizedRel + ms);
                                    }
                                    break;
                                }
                            }
                        }
                    }
                    if (!matchedCurrentValue) {
                        hasUnresolvedValue = true;
                    }
                }
                if (hasUnresolvedValue) {
                    log.warn("Rule state condition value '{}' on device '{}' cannot be resolved to any legal state",
                            condition.getValue(), deviceId);
                    return null;
                }
                if (!matchedExprs.isEmpty()) {
                    // IN: 任一匹配即可 (|)；NOT_IN: 全部不匹配 (&)；其他: 单值用原表达式
                    if ("in".equals(normalizedRel)) {
                        return matchedExprs.size() == 1 ? matchedExprs.get(0) : "(" + String.join(" | ", matchedExprs) + ")";
                    } else if ("not in".equals(normalizedRel)) {
                        return matchedExprs.size() == 1 ? matchedExprs.get(0) : "(" + String.join(" & ", matchedExprs) + ")";
                    } else {
                        return matchedExprs.size() == 1 ? matchedExprs.get(0) : "(" + String.join(" | ", matchedExprs) + ")";
                    }
                }
                log.warn("Rule state condition on device '{}' produced no resolvable expression", deviceId);
                return null;
            }

            boolean isModeAttr = condSmv.getModes() != null && condSmv.getModes().contains(attr);
            DeviceManifest.InternalVariable internalVar = findInternalVariableByName(condSmv, attr);
            DeviceManifest.API signalApi = null;
            if (!isModeAttr && internalVar == null) {
                signalApi = findSignalApiByName(condSmv, attr);
            }
            if (!isModeAttr && internalVar == null && signalApi == null) {
                log.warn("Rule condition attribute '{}' on device '{}' is not a mode/internal variable/API signal",
                        attr, deviceId);
                return null;
            }

            String lhsAttr = attr;
            if (signalApi != null) {
                if (!isSupportedApiSignalRuleRelation(normalizedRel)) {
                    log.warn("Rule API signal condition on device '{}' attribute '{}' does not support relation '{}'",
                            deviceId, attr, normalizedRel);
                    return null;
                }
                lhsAttr = DeviceSmvDataFactory.formatApiSignalName(signalApi.getName());
                if (lhsAttr == null || lhsAttr.isBlank()) {
                    log.warn("Rule API signal condition on device '{}' attribute '{}' cannot resolve signal variable name",
                            deviceId, attr);
                    return null;
                }
            }

            String rhsValue = condition.getValue();
            if (rhsValue != null && isModeAttr) {
                rhsValue = cleanRuleValueByRelation(normalizedRel, rhsValue);
            }
            // BUG 1 fix: 枚举型 InternalVariable 的值也需要去空格，
            // 因为 SmvDeviceModuleBuilder 声明时已做 replace(" ", "")
            if (rhsValue != null && internalVar != null
                    && internalVar.getValues() != null && !internalVar.getValues().isEmpty()) {
                rhsValue = rhsValue.replace(" ", "");
            }
            if (rhsValue != null && signalApi != null) {
                rhsValue = normalizeApiSignalRuleValue(normalizedRel, rhsValue);
                if (rhsValue == null) {
                    log.warn("Rule API signal condition has non-boolean value '{}' for device '{}' attribute '{}'",
                            condition.getValue(), deviceId, attr);
                    return null;
                }
            }
            if (rhsValue == null || rhsValue.isBlank()) {
                log.warn("Rule condition value became null/blank after normalization for device '{}' attribute '{}'",
                        deviceId, attr);
                return null;
            }
            String expr = buildRuleRelationExpr(varName + "." + lhsAttr, normalizedRel, rhsValue);
            if (expr == null || expr.isBlank()) {
                log.warn("Rule condition failed to build relation expression for device '{}' attribute '{}'", deviceId, attr);
                return null;
            }
            return expr;
        }

        // API signal condition
        DeviceManifest manifest = condSmv.getManifest();
        if (manifest == null || manifest.getApis() == null) return null;

        for (DeviceManifest.API api : manifest.getApis()) {
            if (api.getSignal() != null && api.getSignal()
                    && api.getName().equals(condition.getAttribute())) {
                String endState = api.getEndState();
                if (endState == null) break;

                String apiSignal = DeviceSmvDataFactory.formatApiSignalName(api.getName());
                String apiSignalExpr = apiSignal != null
                        ? varName + "." + apiSignal + "=TRUE"
                        : null;

                if (condSmv.getModes() != null && !condSmv.getModes().isEmpty()) {
                    int modeIdx = DeviceSmvDataFactory.getModeIndexOfState(condSmv, endState);
                    if (modeIdx >= 0 && modeIdx < condSmv.getModes().size()) {
                        String mode = condSmv.getModes().get(modeIdx);
                        String cleanEndState = getStateForMode(endState, modeIdx);
                        if (cleanEndState == null || cleanEndState.isEmpty()) break;
                        String stateExpr = varName + "." + mode + "=" + cleanEndState;
                        return apiSignalExpr != null
                                ? "(" + apiSignalExpr + " | " + stateExpr + ")"
                                : stateExpr;
                    }
                } else {
                    // 无模式 fallback
                    String cleanEndState = DeviceSmvDataFactory.cleanStateName(endState);
                    String stateVar = (condSmv.getModes() != null && condSmv.getModes().size() == 1) ? condSmv.getModes().get(0) : "state";
                    String stateExpr = varName + "." + stateVar + "=" + cleanEndState;
                    return apiSignalExpr != null
                            ? "(" + apiSignalExpr + " | " + stateExpr + ")"
                            : stateExpr;
                }
                break;
            }
        }
        log.warn("Rule condition: attribute '{}' on device '{}' did not match any mode, variable, or API signal",
                condition.getAttribute(), deviceId);
        return null;
    }

    private void appendEnvTransitions(StringBuilder content,
                                     List<DeviceVerificationDto> devices,
                                     Map<String, DeviceSmvData> deviceSmvMap) {

        Set<String> processedVars = new HashSet<>();

        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.getEnvVariables() == null) continue;

            for (String varName : smv.getEnvVariables().keySet()) {
                if (processedVars.contains(varName)) continue;
                processedVars.add(varName);

                DeviceManifest.InternalVariable var = smv.getEnvVariables().get(varName);
                String smvVarName = "a_" + varName;

                content.append("\n\tnext(").append(smvVarName).append(") :=\n");
                content.append("\tcase\n");

                for (DeviceVerificationDto dev : devices) {
                    DeviceSmvData transSmv = deviceSmvMap.get(dev.getVarName());
                    if (transSmv == null || transSmv.getManifest() == null ||
                        transSmv.getManifest().getTransitions() == null) continue;

                    for (DeviceManifest.Transition trans : transSmv.getManifest().getTransitions()) {
                        if (trans.getAssignments() == null) continue;

                        for (DeviceManifest.Assignment assignment : trans.getAssignments()) {
                            if (assignment == null || assignment.getAttribute() == null) {
                                throw SmvGenerationException.incompleteTrigger(
                                        transSmv.getVarName(), "Transition '" + trans.getName() + "'",
                                        "assignment or assignment.attribute is null");
                            }
                            if (varName.equals(assignment.getAttribute())) {
                                DeviceManifest.Trigger trigger = trans.getTrigger();
                                if (trigger != null) {
                                    if (trigger.getAttribute() == null || trigger.getRelation() == null
                                            || trigger.getValue() == null || assignment.getValue() == null) {
                                        throw SmvGenerationException.incompleteTrigger(
                                                transSmv.getVarName(), "Transition '" + trans.getName() + "'",
                                                "attribute=" + trigger.getAttribute() + ", relation=" + trigger.getRelation()
                                                        + ", value=" + trigger.getValue() + ", assignValue=" + assignment.getValue());
                                    }
                                    // P4: 若 trigger.attribute 本身是 env var，直接用 a_<attr>
                                    String triggerRef;
                                    if (transSmv.getEnvVariables().containsKey(trigger.getAttribute())) {
                                        triggerRef = "a_" + trigger.getAttribute();
                                    } else {
                                        triggerRef = transSmv.getVarName() + "." + trigger.getAttribute();
                                    }
                                    content.append("\t\t");
                                    // P1-1 修复：增加 startState 约束
                                    if (trans.getStartState() != null && transSmv.getModes() != null && !transSmv.getModes().isEmpty()) {
                                        for (int mi = 0; mi < transSmv.getModes().size(); mi++) {
                                            String ss = getStateForMode(trans.getStartState(), mi);
                                            if (ss != null && !ss.isEmpty()) {
                                                content.append(transSmv.getVarName()).append(".").append(transSmv.getModes().get(mi))
                                                       .append("=").append(ss).append(" & ");
                                            }
                                        }
                                    }
                                    content.append(triggerRef).append(" ")
                                           .append(trigger.getRelation()).append(" ")
                                           .append(trigger.getValue().replace(" ", "")).append(": ").append(assignment.getValue().replace(" ", "")).append(";\n");
                                }
                            }
                        }
                    }
                }

                if (var.getValues() != null && !var.getValues().isEmpty()) {
                    // 枚举型环境变量：非确定性选择所有可能值（与 sample.smv 一致）
                    List<String> cleanValues = new ArrayList<>();
                    for (String v : var.getValues()) {
                        cleanValues.add(v.replace(" ", ""));
                    }
                    content.append("\t\tTRUE: {").append(String.join(", ", cleanValues)).append("};\n");
                } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                    // 数值型环境变量：参照 sample.smv 生成带设备影响率的边界检查
                    appendNumericEnvTransition(content, smvVarName, var, varName, devices, deviceSmvMap);
                } else {
                    content.append("\t\tTRUE: ").append(smvVarName).append(";\n");
                }

                content.append("\tesac;");
            }
        }
    }

    /**
     * 生成数值型环境变量的 next() 转换，参照 sample.smv 格式：
     * 包含设备影响率（如 airconditioner.temperature_rate）和 NaturalChangeRate
     */
    private void appendNumericEnvTransition(StringBuilder content, String smvVarName,
                                            DeviceManifest.InternalVariable var, String varName,
                                            List<DeviceVerificationDto> devices,
                                            Map<String, DeviceSmvData> deviceSmvMap) {
        int upper = var.getUpperBound();
        int lower = var.getLowerBound();

        int[] ncr = parseNaturalChangeRate(var.getNaturalChangeRate(), "env:" + varName);
        int lowerRate = ncr[0], upperRate = ncr[1];

        // 查找所有影响此变量的设备的 rate 变量
        String rateExpr = findImpactRateExpression(varName, devices, deviceSmvMap);

        if (rateExpr != null) {
            // 有设备影响率：生成 sample.smv 风格
            // 上边界: a_var=upper-(rate): {toint(a_var)-1+rate, a_var+rate}
            content.append("\t\t").append(smvVarName).append("=").append(upper)
                   .append("-(").append(rateExpr).append("): {toint(").append(smvVarName)
                   .append(")-1+").append(rateExpr).append(", ").append(smvVarName)
                   .append("+").append(rateExpr).append("};\n");

            // 超上边界: a_var>upper-(rate): {upper}
            content.append("\t\t").append(smvVarName).append(">").append(upper)
                   .append("-(").append(rateExpr).append("): {").append(upper).append("};\n");

            // 下边界: a_var=lower-(rate): {a_var+rate, a_var+1+rate}
            content.append("\t\t").append(smvVarName).append("=").append(lower)
                   .append("-(").append(rateExpr).append("): {").append(smvVarName).append("+")
                   .append(rateExpr).append(", ").append(smvVarName).append("+1+").append(rateExpr).append("};\n");

            // 低于下边界: a_var<lower-(rate): {lower}
            content.append("\t\t").append(smvVarName).append("<").append(lower)
                   .append("-(").append(rateExpr).append("): {").append(lower).append("};\n");

            // 正常范围: {a_var+lowerNcr+rate, a_var+rate, a_var+upperNcr+rate}
            StringBuilder rateSet = new StringBuilder("{");
            if (lowerRate != 0) {
                rateSet.append(formatArithmeticExpr(smvVarName, lowerRate)).append("+").append(rateExpr).append(", ");
            }
            rateSet.append(smvVarName).append("+").append(rateExpr);
            if (upperRate != 0) {
                rateSet.append(", ").append(formatArithmeticExpr(smvVarName, upperRate)).append("+").append(rateExpr);
            }
            rateSet.append("}");
            content.append("\t\tTRUE: ").append(rateSet).append(";\n");
        } else {
            // 无设备影响率：简单的 NaturalChangeRate 变化
            // 边界条件：允许变量朝远离边界的方向变化，但阻止越界
            if (upperRate > 0) {
                // 上边界：禁止继续上升，但允许下降和保持
                StringBuilder upperSet = new StringBuilder("{");
                if (lowerRate < 0) {
                    upperSet.append(formatArithmeticExpr(smvVarName, lowerRate)).append(", ");
                }
                upperSet.append(smvVarName).append("}");
                content.append("\t\t").append(smvVarName).append(">=").append(upper)
                       .append(": ").append(upperSet).append(";\n");
            }
            if (lowerRate < 0) {
                // 下边界：禁止继续下降，但允许上升和保持
                StringBuilder lowerSet = new StringBuilder("{").append(smvVarName);
                if (upperRate > 0) {
                    lowerSet.append(", ").append(formatArithmeticExpr(smvVarName, upperRate));
                }
                lowerSet.append("}");
                content.append("\t\t").append(smvVarName).append("<=").append(lower)
                       .append(": ").append(lowerSet).append(";\n");
            }

            StringBuilder rateSet = new StringBuilder("{");
            boolean first = true;
            if (lowerRate < 0) {
                rateSet.append(formatArithmeticExpr(smvVarName, lowerRate));
                first = false;
            }
            if (!first) rateSet.append(", ");
            rateSet.append(smvVarName);
            if (upperRate > 0) {
                rateSet.append(", ").append(formatArithmeticExpr(smvVarName, upperRate));
            }
            rateSet.append("}");
            content.append("\t\tTRUE: ").append(rateSet).append(";\n");
        }
    }

    /**
     * 查找所有影响指定变量的设备的 rate 表达式
     * 例如：对于 temperature，如果 air_conditioner 的 impactedVariables 包含 temperature，
     * 则返回 "air_conditioner.temperature_rate"
     */
    private String findImpactRateExpression(String varName, List<DeviceVerificationDto> devices,
                                            Map<String, DeviceSmvData> deviceSmvMap) {
        List<String> rateExprs = new ArrayList<>();
        for (DeviceVerificationDto dev : devices) {
            DeviceSmvData devSmv = deviceSmvMap.get(dev.getVarName());
            if (devSmv == null || devSmv.getImpactedVariables() == null) continue;
            if (devSmv.getImpactedVariables().contains(varName)) {
                rateExprs.add(devSmv.getVarName() + "." + varName + "_rate");
            }
        }
        if (rateExprs.isEmpty()) return null;
        // 多个设备影响同一变量时，用加法组合
        return String.join("+", rateExprs);
    }

    private void appendApiSignalTransitions(StringBuilder content,
                                           List<DeviceVerificationDto> devices,
                                           Map<String, DeviceSmvData> deviceSmvMap) {
        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.getManifest() == null || smv.getManifest().getApis() == null) continue;

            String varName = smv.getVarName();

            for (DeviceManifest.API api : smv.getManifest().getApis()) {
                if (api.getSignal() == null || !api.getSignal()) continue;

                String signalName = DeviceSmvDataFactory.formatApiSignalName(api.getName());
                if (signalName == null) {
                    continue;
                }
                
                content.append("\n\tnext(").append(varName).append(".").append(signalName).append(") :=\n");
                content.append("\tcase\n");

                String endState = api.getEndState();
                String startState = api.getStartState();
                
                if (smv.getModes() != null && smv.getModes().size() > 1) {
                    int modeIdx = DeviceSmvDataFactory.getModeIndexOfState(smv, endState);
                    if (modeIdx >= 0 && modeIdx < smv.getModes().size()) {
                        String mode = smv.getModes().get(modeIdx);
                        String cleanEndState = getStateForMode(endState, modeIdx);
                        String cleanStartState = startState != null ? getStateForMode(startState, modeIdx) : "";
                        if (cleanEndState == null || cleanEndState.isEmpty()) continue;
                        if (cleanStartState == null) cleanStartState = "";
                        
                        if (cleanStartState.isEmpty()) {
                            content.append("\t\t").append(varName).append(".").append(mode).append("!=")
                                   .append(cleanEndState).append(" & next(").append(varName).append(".").append(mode)
                                   .append(")=").append(cleanEndState).append(": TRUE;\n");
                        } else {
                            content.append("\t\t").append(varName).append(".").append(mode).append("=")
                                   .append(cleanStartState).append(" & next(").append(varName).append(".").append(mode)
                                   .append(")=").append(cleanEndState).append(": TRUE;\n");
                        }
                    }
                } else {
                    // 无模式 fallback
                    String stateVar = (smv.getModes() != null && smv.getModes().size() == 1) ? smv.getModes().get(0) : "state";
                    String cleanEnd = DeviceSmvDataFactory.cleanStateName(endState);
                    String cleanStart = (startState != null) ? DeviceSmvDataFactory.cleanStateName(startState) : "";
                    if (cleanStart.isEmpty()) {
                        content.append("\t\t").append(varName).append(".").append(stateVar).append("!=").append(cleanEnd)
                               .append(" & next(").append(varName).append(".").append(stateVar).append(")=").append(cleanEnd).append(": TRUE;\n");
                    } else {
                        content.append("\t\t").append(varName).append(".").append(stateVar).append("=").append(cleanStart)
                               .append(" & next(").append(varName).append(".").append(stateVar).append(")=").append(cleanEnd).append(": TRUE;\n");
                    }
                }

                content.append("\t\tTRUE: FALSE;\n");
                content.append("\tesac;");
            }
        }
    }

    /**
     * 为 transition signal（非 API signal）生成 next() 转换。
     * 当设备从 startState 转换到 endState 时 signal=TRUE，否则 FALSE。
     */
    private void appendTransitionSignalTransitions(StringBuilder content,
                                                    List<DeviceVerificationDto> devices,
                                                    Map<String, DeviceSmvData> deviceSmvMap) {
        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null) continue;
            String varName = smv.getVarName();

            for (DeviceSmvData.SignalInfo sig : smv.getSignalVars()) {
                if ("api".equals(sig.getType())) continue;

                content.append("\n\tnext(").append(varName).append(".").append(sig.getName()).append(") :=\n");
                content.append("\tcase\n");

                String endState = sig.getEnd();
                String startState = sig.getStart();
                if (endState != null && smv.getModes() != null && !smv.getModes().isEmpty()) {
                    int modeIdx = DeviceSmvDataFactory.getModeIndexOfState(smv, endState);
                    if (modeIdx >= 0 && modeIdx < smv.getModes().size()) {
                        String mode = smv.getModes().get(modeIdx);
                        String cleanEnd = getStateForMode(endState, modeIdx);
                        String cleanStart = startState != null ? getStateForMode(startState, modeIdx) : null;

                        if (cleanEnd != null && !cleanEnd.isEmpty()) {
                            content.append("\t\t");
                            if (cleanStart != null && !cleanStart.isEmpty()) {
                                content.append(varName).append(".").append(mode).append("=").append(cleanStart)
                                       .append(" & next(").append(varName).append(".").append(mode)
                                       .append(")=").append(cleanEnd).append(": TRUE;\n");
                            } else {
                                content.append(varName).append(".").append(mode).append("!=").append(cleanEnd)
                                       .append(" & next(").append(varName).append(".").append(mode)
                                       .append(")=").append(cleanEnd).append(": TRUE;\n");
                            }
                        }
                    }
                }

                content.append("\t\tTRUE: FALSE;\n");
                content.append("\tesac;");
            }
        }
    }

    private void appendPropertyTransitions(StringBuilder content,
                                           List<DeviceVerificationDto> devices,
                                           List<RuleDto> rules,
                                           Map<String, DeviceSmvData> deviceSmvMap,
                                           boolean isAttack,
                                           PropertyDimension dim) {

        Map<String, List<RuleDto>> rulesByTarget = new LinkedHashMap<>();
        if (rules != null) {
            for (RuleDto rule : rules) {
                if (rule == null || rule.getCommand() == null) continue;
                rulesByTarget.computeIfAbsent(rule.getCommand().getDeviceName(), k -> new ArrayList<>()).add(rule);
            }
        }

        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.isSensor()) continue;

            String varName = smv.getVarName();
            List<RuleDto> deviceRules = rulesByTarget.get(device.getVarName());
            if (deviceRules == null) deviceRules = rulesByTarget.get(smv.getTemplateName());

            if (smv.getModes() == null || smv.getModes().isEmpty()) continue;

            for (int i = 0; i < smv.getModes().size(); i++) {
                String mode = smv.getModes().get(i);
                List<String> modeStates = smv.getModeStates().get(mode);
                if (modeStates == null) continue;

                for (String state : modeStates) {
                    String cleanState = state.replace(" ", "");
                    String propVar = varName + "." + dim.prefix + mode + "_" + cleanState;

                    content.append("\n\tnext(").append(propVar).append(") :=\n");
                    content.append("\tcase\n");

                    if (dim == PropertyDimension.TRUST && isAttack) {
                        content.append("\t\t").append(varName).append(".is_attack=TRUE: untrusted;\n");
                    }

                    if (deviceRules != null) {
                        for (RuleDto rule : deviceRules) {
                            if (rule.getCommand() == null || rule.getCommand().getAction() == null) continue;
                            DeviceManifest.API api = DeviceSmvDataFactory.findApi(smv.getManifest(), rule.getCommand().getAction());
                            if (api == null) continue;

                            String endState = getStateForMode(api.getEndState(), i);
                            if (endState != null && endState.replace(" ", "").equals(cleanState)) {
                                content.append("\t\t");
                                appendRuleConditions(content, rule, deviceSmvMap);
                                content.append(" & (");
                                appendRulePropertyConditions(content, rule, deviceSmvMap, dim);
                                // content 隐私传播：规则携带 contentDevice.content 时追加 content privacy 条件
                                if (dim == PropertyDimension.PRIVACY) {
                                    String contentCond = buildContentPrivacyCondition(rule, deviceSmvMap);
                                    if (contentCond != null) {
                                        content.append(" | ").append(contentCond);
                                    }
                                }
                                content.append("): ").append(dim.activeValue).append(";\n");

                                if (dim == PropertyDimension.TRUST) {
                                    content.append("\t\t");
                                    appendRuleConditions(content, rule, deviceSmvMap);
                                    content.append(": untrusted;\n");
                                }
                            }
                        }
                    }

                    content.append("\t\tTRUE: ").append(propVar).append(";\n");
                    content.append("\tesac;");
                }
            }
        }
    }

    /**
     * 为 actuator 设备的变量级 trust/privacy 生成 next() 转换（自保持）。
     * 这些变量在 SmvDeviceModuleBuilder 中声明为 VAR，必须有 next() 否则 NuSMV 视为非确定性。
     */
    private void appendVariablePropertyTransitions(StringBuilder content,
                                                    List<DeviceVerificationDto> devices,
                                                    Map<String, DeviceSmvData> deviceSmvMap,
                                                    PropertyDimension dim) {
        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.isSensor()) continue;

            String varName = smv.getVarName();
            for (DeviceManifest.InternalVariable var : smv.getVariables()) {
                String propVar = varName + "." + dim.prefix + var.getName();
                content.append("\n\tnext(").append(propVar).append(") := ").append(propVar).append(";");
            }
        }
    }

    private void appendRulePropertyConditions(StringBuilder content, RuleDto rule,
                                              Map<String, DeviceSmvData> deviceSmvMap,
                                              PropertyDimension dim) {
        if (rule.getConditions() == null || rule.getConditions().isEmpty()) {
            content.append("TRUE");
            return;
        }

        List<String> parts = new ArrayList<>();
        for (RuleDto.Condition condition : rule.getConditions()) {
            if (condition == null || condition.getDeviceName() == null) continue;
            DeviceSmvData condSmv = DeviceSmvDataFactory.findDeviceSmvData(condition.getDeviceName(), deviceSmvMap);
            if (condSmv == null || condSmv.getManifest() == null) continue;

            String part = buildPropertyConditionPart(condition, condSmv, condSmv.getVarName(), condSmv.getManifest(), dim);
            if (part != null && !part.isEmpty()) parts.add(part);
        }

        // C2 修复：所有条件源都可信时才传播 trusted，用 & 而非 |
        content.append(parts.isEmpty() ? "TRUE" : String.join(" & ", parts));
    }

    private String buildPropertyConditionPart(RuleDto.Condition condition, DeviceSmvData condSmv,
                                              String condVarName, DeviceManifest deviceManifest,
                                              PropertyDimension dim) {
        if (condition.getRelation() == null) {
            if (deviceManifest.getApis() != null) {
                for (DeviceManifest.API api : deviceManifest.getApis()) {
                    if (api.getName().equals(condition.getAttribute()) && Boolean.TRUE.equals(api.getSignal())) {
                        String endState = api.getEndState();
                        if (endState == null) break;
                        if (condSmv.getModes() != null && !condSmv.getModes().isEmpty()) {
                            int modeIdx = DeviceSmvDataFactory.getModeIndexOfState(condSmv, endState);
                            if (modeIdx >= 0 && modeIdx < condSmv.getModes().size()) {
                                String cleanEndState = getStateForMode(endState, modeIdx);
                                if (cleanEndState == null || cleanEndState.isEmpty()) break;
                                return condVarName + "." + dim.prefix + condSmv.getModes().get(modeIdx) + "_" + cleanEndState + "=" + dim.activeValue;
                            }
                        } else {
                            String cleanEndState = DeviceSmvDataFactory.cleanStateName(endState);
                            String modePrefix = (condSmv.getModes() != null && condSmv.getModes().size() == 1) ? condSmv.getModes().get(0) + "_" : "";
                            return condVarName + "." + dim.prefix + modePrefix + cleanEndState + "=" + dim.activeValue;
                        }
                        break;
                    }
                }
            }
        } else {
            if (deviceManifest.getInternalVariables() != null) {
                for (DeviceManifest.InternalVariable var : deviceManifest.getInternalVariables()) {
                    if (var.getName().equals(condition.getAttribute())) {
                        return condVarName + "." + dim.prefix + var.getName() + "=" + dim.activeValue;
                    }
                }
            }

            if ("=".equals(normalizeRuleRelation(condition.getRelation())) && condition.getValue() != null) {
                String stateValue = condition.getValue().replace(" ", "");
                if (condSmv.getModes() != null && !condSmv.getModes().isEmpty()) {
                    // 先检查 attribute 是否是 mode 名
                    if (condSmv.getModes().contains(condition.getAttribute())) {
                        return condVarName + "." + dim.prefix + condition.getAttribute() + "_" + stateValue + "=" + dim.activeValue;
                    }
                    // M2 修复：多模式设备 value 含分号时，解析为各 mode 的状态
                    if (stateValue.contains(";") && condSmv.getModes().size() > 1) {
                        String[] parts = stateValue.split(";");
                        List<String> propParts = new ArrayList<>();
                        for (int mi = 0; mi < parts.length && mi < condSmv.getModes().size(); mi++) {
                            String part = parts[mi].trim();
                            if (!part.isEmpty()) {
                                propParts.add(condVarName + "." + dim.prefix + condSmv.getModes().get(mi) + "_" + part + "=" + dim.activeValue);
                            }
                        }
                        if (!propParts.isEmpty()) {
                            return propParts.size() == 1 ? propParts.get(0) : "(" + String.join(" & ", propParts) + ")";
                        }
                    }
                    // 否则按 value 在哪个 mode 的状态列表中查找
                    for (String mode : condSmv.getModes()) {
                        List<String> modeStates = condSmv.getModeStates().get(mode);
                        if (modeStates != null && modeStates.contains(stateValue)) {
                            return condVarName + "." + dim.prefix + mode + "_" + stateValue + "=" + dim.activeValue;
                        }
                    }
                    return condVarName + "." + dim.prefix + condSmv.getModes().get(0) + "_" + stateValue + "=" + dim.activeValue;
                } else {
                    return condVarName + "." + dim.prefix + stateValue + "=" + dim.activeValue;
                }
            }
        }
        return null;
    }

    /**
     * 当规则命令携带 contentDevice.content 时，生成 content 隐私条件。
     * 例如规则 "THEN Facebook.post(MobilePhone.photo)" → "mobilephone.privacy_photo=private"
     */
    private String buildContentPrivacyCondition(RuleDto rule, Map<String, DeviceSmvData> deviceSmvMap) {
        if (rule.getCommand() == null) return null;
        String contentDevice = rule.getCommand().getContentDevice();
        String contentName = rule.getCommand().getContent();
        if (contentDevice == null || contentDevice.isBlank() || contentName == null || contentName.isBlank()) return null;

        DeviceSmvData contentSmv = DeviceSmvDataFactory.findDeviceSmvData(contentDevice, deviceSmvMap);
        if (contentSmv == null) return null;

        // 验证 content 确实存在于该设备
        for (DeviceSmvData.ContentInfo ci : contentSmv.getContents()) {
            if (contentName.equals(ci.getName())) {
                return contentSmv.getVarName() + ".privacy_" + contentName + "=private";
            }
        }
        return null;
    }

    /**
     * 为 IsChangeable=true 的 content 生成 next() 转换。
     * 当规则命令引用了该 content（如 THEN Facebook.post(MobilePhone.photo)）时，
     * 规则触发会将 content 隐私设为 private；否则自保持。
     */
    private void appendContentPrivacyTransitions(StringBuilder content,
                                                  List<DeviceVerificationDto> devices,
                                                  List<RuleDto> rules,
                                                  Map<String, DeviceSmvData> deviceSmvMap) {
        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.getContents() == null) continue;

            String varName = smv.getVarName();
            for (DeviceSmvData.ContentInfo ci : smv.getContents()) {
                if (!ci.isChangeable()) continue;

                String propVar = varName + ".privacy_" + ci.getName();

                // 收集所有引用此 content 的规则
                List<RuleDto> matchingRules = findRulesReferencingContent(
                        rules, device.getVarName(), smv.getTemplateName(), ci.getName());

                if (matchingRules.isEmpty()) {
                    // 无规则引用此 content，纯自保持
                    content.append("\n\tnext(").append(propVar).append(") := ").append(propVar).append(";");
                } else {
                    content.append("\n\tnext(").append(propVar).append(") :=\n");
                    content.append("\tcase\n");
                    for (RuleDto rule : matchingRules) {
                        content.append("\t\t");
                        appendRuleConditions(content, rule, deviceSmvMap);
                        content.append(": private;\n");
                    }
                    content.append("\t\tTRUE: ").append(propVar).append(";\n");
                    content.append("\tesac;");
                }
            }
        }
    }

    /**
     * 查找所有 command.contentDevice 匹配指定设备且 command.content 匹配指定 content 名称的规则。
     */
    private List<RuleDto> findRulesReferencingContent(List<RuleDto> rules,
                                                       String deviceVarName, String templateName,
                                                       String contentName) {
        List<RuleDto> result = new ArrayList<>();
        if (rules == null) return result;
        for (RuleDto rule : rules) {
            if (rule == null || rule.getCommand() == null) continue;
            String cd = rule.getCommand().getContentDevice();
            String cn = rule.getCommand().getContent();
            if (cn == null || !cn.equals(contentName)) continue;
            if (cd != null && (cd.equals(deviceVarName) || cd.equals(templateName))) {
                result.add(rule);
            }
        }
        return result;
    }

    private void appendVariableRateTransitions(StringBuilder content,
                                              List<DeviceVerificationDto> devices,
                                              Map<String, DeviceSmvData> deviceSmvMap) {
        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.getImpactedVariables() == null || smv.getManifest() == null) continue;

            String varName = smv.getVarName();

            for (String varName2 : smv.getImpactedVariables()) {
                boolean isEnum = false;
                for (DeviceManifest.InternalVariable var : smv.getManifest().getInternalVariables()) {
                    if (var.getName().equals(varName2) && var.getValues() != null) {
                        isEnum = true;
                        break;
                    }
                }
                if (isEnum) continue;

                content.append("\n\tnext(").append(varName).append(".").append(varName2).append("_rate) :=\n");
                content.append("\tcase\n");

                if (smv.getManifest().getWorkingStates() != null) {
                    for (DeviceManifest.WorkingState state : smv.getManifest().getWorkingStates()) {
                        if (state.getDynamics() == null) continue;
                        
                        for (DeviceManifest.Dynamic dynamic : state.getDynamics()) {
                            if (varName2.equals(dynamic.getVariableName())) {
                                if (smv.getModes() != null && !smv.getModes().isEmpty()) {
                                    String[] states = state.getName().split(";");
                                    content.append("\t\t");
                                    for (int c = 0; c < smv.getModes().size() && c < states.length; c++) {
                                        if (c > 0) content.append(" & ");
                                        content.append(varName).append(".").append(smv.getModes().get(c))
                                               .append("=").append(states[c].replace(" ", ""));
                                    }
                                    content.append(": ").append(dynamic.getChangeRate()).append(";\n");
                                } else {
                                    log.warn("Device '{}': has ImpactedVariable '{}' with Dynamics but no modes, skipping rate condition for state '{}'",
                                            varName, varName2, state.getName());
                                }
                            }
                        }
                    }
                }

                content.append("\t\tTRUE: 0;\n");
                content.append("\tesac;");
            }
        }
    }

    private void appendInternalVariableTransitions(StringBuilder content,
                                                  List<DeviceVerificationDto> devices,
                                                  Map<String, DeviceSmvData> deviceSmvMap,
                                                  boolean isAttack) {
        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.getManifest() == null || smv.getManifest().getInternalVariables() == null) continue;

            String varName = smv.getVarName();
            boolean isSensor = smv.isSensor();

            for (DeviceManifest.InternalVariable var : smv.getManifest().getInternalVariables()) {
                if (var.getIsInside() == null || !var.getIsInside()) {
                    continue;
                }

                content.append("\n\tnext(").append(varName).append(".").append(var.getName()).append(") :=\n");
                content.append("\tcase\n");

                if (isAttack && isSensor) {
                    content.append("\t\t").append(varName).append(".is_attack=TRUE: ");
                    if (var.getValues() != null && !var.getValues().isEmpty()) {
                        List<String> cleanVals = new ArrayList<>();
                        for (String v : var.getValues()) {
                            cleanVals.add(v.replace(" ", ""));
                        }
                        content.append("{").append(String.join(", ", cleanVals)).append("};\n");
                    } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                        content.append(var.getLowerBound()).append("..").append(var.getUpperBound()).append(";\n");
                    } else {
                        content.append("0..100;\n");
                    }
                }

                if (smv.getManifest().getTransitions() != null) {
                    for (DeviceManifest.Transition trans : smv.getManifest().getTransitions()) {
                        if (trans.getAssignments() == null) continue;
                        
                        for (DeviceManifest.Assignment assignment : trans.getAssignments()) {
                            if (assignment == null || assignment.getAttribute() == null) {
                                throw SmvGenerationException.incompleteTrigger(
                                        smv.getVarName(), "Transition '" + trans.getName() + "'",
                                        "assignment or assignment.attribute is null");
                            }
                            if (var.getName().equals(assignment.getAttribute())) {
                                DeviceManifest.Trigger trigger = trans.getTrigger();
                                if (trigger != null) {
                                    if (trigger.getAttribute() == null || trigger.getRelation() == null
                                            || trigger.getValue() == null || assignment.getValue() == null) {
                                        throw SmvGenerationException.incompleteTrigger(
                                                smv.getVarName(), "Transition '" + trans.getName() + "'",
                                                "attribute=" + trigger.getAttribute() + ", relation=" + trigger.getRelation()
                                                        + ", value=" + trigger.getValue() + ", assignValue=" + assignment.getValue());
                                    }
                                    content.append("\t\t");
                                    // P1-1 修复：增加 startState 约束
                                    if (trans.getStartState() != null && smv.getModes() != null && !smv.getModes().isEmpty()) {
                                        for (int mi = 0; mi < smv.getModes().size(); mi++) {
                                            String ss = getStateForMode(trans.getStartState(), mi);
                                            if (ss != null && !ss.isEmpty()) {
                                                content.append(varName).append(".").append(smv.getModes().get(mi))
                                                       .append("=").append(ss).append(" & ");
                                            }
                                        }
                                    }
                                    // Keep trigger reference resolution consistent with appendEnvTransitions.
                                    String triggerRef;
                                    if (smv.getEnvVariables().containsKey(trigger.getAttribute())) {
                                        triggerRef = "a_" + trigger.getAttribute();
                                    } else {
                                        triggerRef = varName + "." + trigger.getAttribute();
                                    }
                                    content.append(triggerRef).append(" ")
                                           .append(trigger.getRelation()).append(" ")
                                           .append(trigger.getValue().replace(" ", "")).append(": ").append(assignment.getValue().replace(" ", "")).append(";\n");
                                }
                            }
                        }
                    }
                }

                if (var.getValues() == null || var.getValues().isEmpty()) {
                    String impactedRate = "";
                    if (smv.getImpactedVariables() != null && smv.getImpactedVariables().contains(var.getName())) {
                        impactedRate = varName + "." + var.getName() + "_rate";
                    }

                    int[] ncrParsed = parseNaturalChangeRate(var.getNaturalChangeRate(), "internal:" + var.getName());
                    int lowerNcr = ncrParsed[0], upperNcr = ncrParsed[1];

                    String varRef = varName + "." + var.getName();

                    // 边界检查：防止溢出 NuSMV 范围
                    if (var.getUpperBound() != null && (upperNcr > 0 || !impactedRate.isEmpty())) {
                        if (impactedRate.isEmpty()) {
                            // 无设备影响率：允许下降和保持，禁止上升
                            StringBuilder upperSet = new StringBuilder("{");
                            if (lowerNcr < 0) {
                                upperSet.append(formatArithmeticExpr(varRef, lowerNcr)).append(", ");
                            }
                            upperSet.append(varRef).append("}");
                            content.append("\t\t").append(varRef).append(">=").append(var.getUpperBound())
                                   .append(": ").append(upperSet).append(";\n");
                        } else {
                            content.append("\t\t").append(varRef).append(">=").append(var.getUpperBound())
                                   .append(": ").append(var.getUpperBound()).append(";\n");
                        }
                    }
                    if (var.getLowerBound() != null && (lowerNcr < 0 || !impactedRate.isEmpty())) {
                        if (impactedRate.isEmpty()) {
                            // 无设备影响率：允许上升和保持，禁止下降
                            StringBuilder lowerSet = new StringBuilder("{").append(varRef);
                            if (upperNcr > 0) {
                                lowerSet.append(", ").append(formatArithmeticExpr(varRef, upperNcr));
                            }
                            lowerSet.append("}");
                            content.append("\t\t").append(varRef).append("<=").append(var.getLowerBound())
                                   .append(": ").append(lowerSet).append(";\n");
                        } else {
                            content.append("\t\t").append(varRef).append("<=").append(var.getLowerBound())
                                   .append(": ").append(var.getLowerBound()).append(";\n");
                        }
                    }

                    // 生成变化集合
                    StringBuilder rateSet = new StringBuilder("{");
                    boolean first = true;
                    if (lowerNcr < 0) {
                        rateSet.append(formatArithmeticExpr(varRef, lowerNcr));
                        if (!impactedRate.isEmpty()) rateSet.append("+").append(impactedRate);
                        first = false;
                    }
                    if (!first) rateSet.append(", ");
                    rateSet.append(varRef);
                    if (!impactedRate.isEmpty()) rateSet.append("+").append(impactedRate);
                    if (upperNcr > 0) {
                        rateSet.append(", ").append(formatArithmeticExpr(varRef, upperNcr));
                        if (!impactedRate.isEmpty()) rateSet.append("+").append(impactedRate);
                    }
                    rateSet.append("}");
                    content.append("\t\tTRUE: ").append(rateSet).append(";\n");
                } else {
                    // 枚举型变量：检查 Dynamics.Value 生成状态依赖赋值
                    if (smv.getManifest().getWorkingStates() != null) {
                        for (DeviceManifest.WorkingState state : smv.getManifest().getWorkingStates()) {
                            if (state.getDynamics() == null) continue;
                            for (DeviceManifest.Dynamic dynamic : state.getDynamics()) {
                                if (var.getName().equals(dynamic.getVariableName()) && dynamic.getValue() != null) {
                                    String cleanValue = dynamic.getValue().replace(" ", "");
                                    if (smv.getModes() != null && !smv.getModes().isEmpty()) {
                                        String[] stateNames = state.getName().split(";");
                                        content.append("\t\t");
                                        for (int c = 0; c < smv.getModes().size() && c < stateNames.length; c++) {
                                            if (c > 0) content.append(" & ");
                                            content.append(varName).append(".").append(smv.getModes().get(c))
                                                   .append("=").append(stateNames[c].replace(" ", ""));
                                        }
                                        content.append(": ").append(cleanValue).append(";\n");
                                    }
                                }
                            }
                        }
                    }
                    List<String> cleanVals = new ArrayList<>();
                    for (String v : var.getValues()) {
                        cleanVals.add(v.replace(" ", ""));
                    }
                    content.append("\t\tTRUE: {").append(String.join(", ", cleanVals)).append("};\n");
                }

                content.append("\tesac;");
            }
        }
    }

    /**
     * 从分号分隔的多模式状态字符串中提取指定模式索引的状态值。
     * 例如 "locked;off" 在 modeIndex=0 时返回 "locked"，modeIndex=1 时返回 "off"。
     */
    private String getStateForMode(String multiModeState, int modeIndex) {
        if (multiModeState == null) return null;
        String[] states = multiModeState.split(";");
        if (modeIndex < states.length) {
            return DeviceSmvDataFactory.cleanStateName(states[modeIndex]);
        }
        return null;
    }

    private String formatArithmeticExpr(String varRef, int rate) {
        if (rate == 0) return varRef;
        if (rate > 0) return varRef + " + " + rate;
        return varRef + " - " + Math.abs(rate);
    }

    /**
     * 解析 NaturalChangeRate 字符串为 [lowerRate, upperRate]。
     * 格式：单值 "3" 或范围 "[-1,2]"。
     * 返回 int[2]，[0]=lowerRate, [1]=upperRate。
     */
    private int[] parseNaturalChangeRate(String ncr, String contextName) {
        int lowerRate = 0, upperRate = 0;
        if (ncr != null && !ncr.isEmpty()) {
            String[] parts = ncr.replaceAll("[\\[\\]]", "").split(",");
            try {
                if (parts.length >= 2) {
                    lowerRate = Integer.parseInt(parts[0].trim());
                    upperRate = Integer.parseInt(parts[1].trim());
                } else if (parts.length == 1) {
                    int rate = Integer.parseInt(parts[0].trim());
                    if (rate > 0) upperRate = rate;
                    else lowerRate = rate;
                }
            } catch (NumberFormatException e) {
                log.warn("Failed to parse NaturalChangeRate for {}: {}", contextName, ncr);
            }
        }
        return new int[]{lowerRate, upperRate};
    }

    private Map<String, String> resolveEnvVarInitValues(Map<String, Map<String, String>> envVarInitSources) {
        Map<String, String> resolved = new LinkedHashMap<>();
        for (Map.Entry<String, Map<String, String>> entry : envVarInitSources.entrySet()) {
            String varName = entry.getKey();
            Map<String, String> sourceValues = entry.getValue();
            Set<String> uniqueValues = new LinkedHashSet<>(sourceValues.values());
            if (uniqueValues.size() > 1) {
                StringBuilder details = new StringBuilder();
                boolean first = true;
                for (Map.Entry<String, String> sv : sourceValues.entrySet()) {
                    if (!first) details.append(", ");
                    first = false;
                    details.append("'").append(sv.getKey()).append("'=").append(sv.getValue());
                }
                throw SmvGenerationException.envVarConflict(varName,
                        "conflicting user init values across devices: " + details);
            }
            resolved.put(varName, uniqueValues.iterator().next());
        }
        return resolved;
    }

    /**
     * 校验环境变量初始值是否在声明范围内。
     * 对于数值型变量，超出范围时 clamp 到边界并记录警告。
     * 对于枚举型变量，检查值是否在枚举列表中。
     */
    private String validateEnvVarInitValue(String varName, String userInit,
                                           DeviceManifest.InternalVariable var, boolean isAttack, int intensity) {
        if (var.getValues() != null && !var.getValues().isEmpty()) {
            List<String> cleanValues = new ArrayList<>();
            for (String v : var.getValues()) cleanValues.add(v.replace(" ", ""));
            String cleanInit = userInit.replace(" ", "");
            if (!cleanValues.contains(cleanInit)) {
                log.warn("Env variable '{}': init value '{}' not in enum {}, using first value '{}'",
                        varName, userInit, cleanValues, cleanValues.get(0));
                return cleanValues.get(0);
            }
            return cleanInit;
        } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
            try {
                int value = Integer.parseInt(userInit.trim());
                int lower = var.getLowerBound();
                int upper = var.getUpperBound();
                if (isAttack) {
                    int range = upper - lower;
                    upper = upper + (int)(range / 5.0 * intensity / 50.0);
                }
                if (value < lower) {
                    log.warn("Env variable '{}': init value {} below lower bound {}, clamped", varName, value, lower);
                    return String.valueOf(lower);
                }
                if (value > upper) {
                    log.warn("Env variable '{}': init value {} above upper bound {}, clamped", varName, value, upper);
                    return String.valueOf(upper);
                }
                return userInit.trim();
            } catch (NumberFormatException e) {
                log.warn("Env variable '{}': init value '{}' is not a valid integer, ignored", varName, userInit);
                return null;
            }
        }
        // 无枚举/无边界定义时，变量在 main 中以 0..100 声明，初值也应保持同范围整数
        try {
            int value = Integer.parseInt(userInit.trim());
            if (value < 0) {
                log.warn("Env variable '{}': init value {} below default lower bound 0, clamped", varName, value);
                return "0";
            }
            if (value > 100) {
                log.warn("Env variable '{}': init value {} above default upper bound 100, clamped", varName, value);
                return "100";
            }
            return String.valueOf(value);
        } catch (NumberFormatException e) {
            log.warn("Env variable '{}': init value '{}' is not a valid integer for default range 0..100, ignored",
                    varName, userInit);
            return null;
        }
    }

    /**
     * 将前端关系符归一化为 NuSMV 运算符。
     */
    private static String normalizeRuleRelation(String relation) {
        if (relation == null) return "=";
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

    private static boolean isSupportedRuleRelation(String relation) {
        return "=".equals(relation)
                || "!=".equals(relation)
                || ">".equals(relation)
                || ">=".equals(relation)
                || "<".equals(relation)
                || "<=".equals(relation)
                || "in".equals(relation)
                || "not in".equals(relation);
    }

    /**
     * 将 IN/NOT_IN 展开为 NuSMV 的 (x=a | x=b) 或 (x!=a & x!=b)。
     * 非集合运算符直接返回 left + relation + value。
     */
    private static String buildRuleRelationExpr(String left, String relation, String value) {
        if ("in".equals(relation) || "not in".equals(relation)) {
            String[] parts = value.split("[,;|]");
            List<String> cleaned = new ArrayList<>();
            for (String p : parts) {
                String trimmed = p.trim();
                if (!trimmed.isEmpty()) {
                    cleaned.add(trimmed);
                }
            }
            if (cleaned.isEmpty()) {
                log.warn("Empty value list for '{}' relation on {}", relation, left);
                return null;
            }
            String op = "in".equals(relation) ? "=" : "!=";
            String join = "in".equals(relation) ? " | " : " & ";
            if (cleaned.size() == 1) {
                return left + op + cleaned.get(0);
            }
            StringBuilder sb = new StringBuilder("(");
            for (int i = 0; i < cleaned.size(); i++) {
                if (i > 0) sb.append(join);
                sb.append(left).append(op).append(cleaned.get(i));
            }
            sb.append(")");
            return sb.toString();
        }
        return left + relation + value;
    }

    /**
     * 按 ,;| 拆分值列表（用于 IN/NOT_IN），单值时返回包含原值的单元素列表。
     */
    private static List<String> splitRuleValues(String value) {
        if (value == null) return List.of();
        String[] parts = value.split("[,;|]");
        List<String> result = new ArrayList<>();
        for (String p : parts) {
            String trimmed = p.trim();
            if (!trimmed.isEmpty()) {
                result.add(trimmed);
            }
        }
        return result;
    }

    /**
     * 对 mode 状态值做 cleanStateName，IN/NOT_IN 时逐个清理再用逗号拼接。
     */
    private static String cleanRuleValueByRelation(String normalizedRelation, String value) {
        if (value == null) return null;
        if ("in".equals(normalizedRelation) || "not in".equals(normalizedRelation)) {
            List<String> parts = splitRuleValues(value);
            StringBuilder sb = new StringBuilder();
            for (int i = 0; i < parts.size(); i++) {
                if (i > 0) sb.append(",");
                sb.append(DeviceSmvDataFactory.cleanStateName(parts.get(i)));
            }
            return sb.toString();
        }
        return DeviceSmvDataFactory.cleanStateName(value);
    }

    private static DeviceManifest.InternalVariable findInternalVariableByName(DeviceSmvData smv, String attr) {
        if (smv == null || attr == null || smv.getManifest() == null || smv.getManifest().getInternalVariables() == null) {
            return null;
        }
        for (DeviceManifest.InternalVariable iv : smv.getManifest().getInternalVariables()) {
            if (attr.equals(iv.getName())) {
                return iv;
            }
        }
        return null;
    }

    private static DeviceManifest.API findSignalApiByName(DeviceSmvData smv, String attr) {
        if (smv == null || attr == null || smv.getManifest() == null || smv.getManifest().getApis() == null) {
            return null;
        }
        for (DeviceManifest.API api : smv.getManifest().getApis()) {
            if (attr.equals(api.getName()) && Boolean.TRUE.equals(api.getSignal())) {
                return api;
            }
        }
        return null;
    }

    private static boolean isSupportedApiSignalRuleRelation(String relation) {
        return "=".equals(relation)
                || "!=".equals(relation)
                || "in".equals(relation)
                || "not in".equals(relation);
    }

    private static String normalizeApiSignalRuleValue(String relation, String value) {
        if (value == null) return null;
        if ("in".equals(relation) || "not in".equals(relation)) {
            List<String> values = splitRuleValues(value);
            if (values.isEmpty()) return null;
            List<String> normalized = new ArrayList<>();
            for (String item : values) {
                String boolLiteral = normalizeBooleanLiteral(item);
                if (boolLiteral == null) return null;
                normalized.add(boolLiteral);
            }
            return String.join(",", normalized);
        }
        return normalizeBooleanLiteral(value);
    }

    private static String normalizeBooleanLiteral(String raw) {
        if (raw == null) return null;
        String normalized = raw.trim();
        if ("TRUE".equalsIgnoreCase(normalized)) return "TRUE";
        if ("FALSE".equalsIgnoreCase(normalized)) return "FALSE";
        return null;
    }
}
