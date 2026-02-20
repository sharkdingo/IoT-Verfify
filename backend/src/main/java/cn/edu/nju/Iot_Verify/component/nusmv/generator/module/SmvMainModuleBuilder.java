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
        if (isAttack && intensity > 0) {
            content.append("\nFROZENVAR");
            content.append("\n\tintensity: 0..50;");
        }

        content.append("\nVAR\n");

        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null) continue;

            String moduleName = smv.getModuleName();
            String varName = smv.getVarName();
            content.append("\t").append(varName).append(": ").append(moduleName).append(";\n");
        }

        Set<String> declaredEnvVars = new HashSet<>();
        // 收集环境变量的用户初始值，用于生成 init()
        Map<String, String> envVarInitValues = new LinkedHashMap<>();
        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.getEnvVariables() == null) continue;

            for (String varName : smv.getEnvVariables().keySet()) {
                if (!declaredEnvVars.contains(varName)) {
                    declaredEnvVars.add(varName);
                    DeviceManifest.InternalVariable var = smv.getEnvVariables().get(varName);
                    content.append("\ta_").append(varName).append(": ");
                    if (var.getValues() != null && !var.getValues().isEmpty()) {
                        List<String> cleanValues = new ArrayList<>();
                        for (String v : var.getValues()) {
                            cleanValues.add(v.replace(" ", ""));
                        }
                        content.append("{").append(String.join(", ", cleanValues)).append("};\n");
                    } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                        int lower = var.getLowerBound();
                        int upper = var.getUpperBound();
                        // 攻击模式下扩大环境变量范围，模拟传感器数据篡改
                        if (isAttack) {
                            int range = upper - lower;
                            int expansion = Math.max(10, range / 5);
                            upper = upper + expansion;
                        }
                        content.append(lower).append("..").append(upper).append(";\n");
                    } else {
                        // NuSMV has no "integer" type; use a safe default range
                        content.append("0..100;\n");
                    }
                    // 记录用户提供的初始值（校验范围）
                    String userInit = smv.getVariableValues().get(varName);
                    if (userInit != null && !userInit.isBlank()) {
                        String validatedInit = validateEnvVarInitValue(varName, userInit, var, isAttack);
                        if (validatedInit != null) {
                            envVarInitValues.put(varName, validatedInit);
                        }
                    }
                }
            }
        }

        content.append("\nASSIGN");

        // 生成环境变量的 init()（使用用户指定的初始值）
        for (Map.Entry<String, String> entry : envVarInitValues.entrySet()) {
            content.append("\n\tinit(a_").append(entry.getKey()).append(") := ")
                   .append(entry.getValue()).append(";");
        }

        if (isAttack && intensity > 0) {
            content.append("\n\tinit(intensity) := 0");
            for (DeviceVerificationDto device : devices) {
                DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
                if (smv != null) {
                    String varName = smv.getVarName();
                    content.append(" + toint(").append(varName).append(".is_attack)");
                }
            }
            content.append(";\n");
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
                               .append(" := a_").append(var.getName()).append(";\n");
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
                    content.append("\tesac;\n");
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
            if (condition == null) continue;

            String part = buildSingleCondition(condition, deviceSmvMap);
            if (part != null && !part.isEmpty()) {
                parts.add(part);
            }
        }

        if (parts.isEmpty()) {
            content.append("TRUE");
        } else {
            content.append(String.join(" & ", parts));
        }
    }

    private String buildSingleCondition(RuleDto.Condition condition, Map<String, DeviceSmvData> deviceSmvMap) {
        String deviceId = condition.getDeviceName();
        DeviceSmvData condSmv = DeviceSmvDataFactory.findDeviceSmvData(deviceId, deviceSmvMap);

        if (condSmv == null) {
            log.warn("Rule condition references unknown device '{}', skipping to avoid undefined SMV variable", deviceId);
            return null;
        }

        String varName = condSmv.getVarName();
        String attr = condition.getAttribute();

        if (condition.getRelation() != null) {
            // relation 非空时 value 也必须非空，否则无法生成有效条件
            if (condition.getValue() == null) {
                log.warn("Rule condition has relation '{}' but null value for device '{}', skipping",
                        condition.getRelation(), deviceId);
                return null;
            }
            // M1/M2: 当 attribute="state" 时，解析为实际的 mode 变量名
            if ("state".equals(attr) && condSmv.getModes() != null && !condSmv.getModes().isEmpty()) {
                String value = condition.getValue();
                String cleanValue = DeviceSmvDataFactory.cleanStateName(value);
                List<String> matchedExprs = new ArrayList<>();
                for (String mode : condSmv.getModes()) {
                    List<String> modeStateList = condSmv.getModeStates().get(mode);
                    if (modeStateList != null) {
                        for (String ms : modeStateList) {
                            String suffix = ms.startsWith(mode + "_") ? ms.substring(mode.length() + 1) : ms;
                            if (suffix.equals(cleanValue) || ms.equals(cleanValue)) {
                                matchedExprs.add(varName + "." + mode + normalizeRuleRelation(condition.getRelation()) + ms);
                                break; // 每个 mode 最多匹配一个状态
                            }
                        }
                    }
                }
                if (matchedExprs.size() == 1) {
                    return matchedExprs.get(0);
                } else if (matchedExprs.size() > 1) {
                    return "(" + String.join(" | ", matchedExprs) + ")";
                }
                // 单 mode fallback：直接用 mode 名替代 "state"
                if (condSmv.getModes().size() == 1) {
                    attr = condSmv.getModes().get(0);
                }
            }
            String rhsValue = condition.getValue();
            if (rhsValue != null && condSmv.getModes() != null && condSmv.getModes().contains(attr)) {
                rhsValue = DeviceSmvDataFactory.cleanStateName(rhsValue);
            }
            // BUG 1 fix: 枚举型 InternalVariable 的值也需要去空格，
            // 因为 SmvDeviceModuleBuilder 声明时已做 replace(" ", "")
            if (rhsValue != null && condSmv.getManifest() != null
                    && condSmv.getManifest().getInternalVariables() != null) {
                for (DeviceManifest.InternalVariable iv : condSmv.getManifest().getInternalVariables()) {
                    if (iv.getName().equals(attr) && iv.getValues() != null && !iv.getValues().isEmpty()) {
                        rhsValue = rhsValue.replace(" ", "");
                        break;
                    }
                }
            }
            return varName + "." + attr + normalizeRuleRelation(condition.getRelation()) + rhsValue;
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
                                    if (isEnvVariable(trigger.getAttribute(), devices, deviceSmvMap)) {
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

                content.append("\tesac;\n");
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
            if (upperRate > 0) {
                content.append("\t\t").append(smvVarName).append(">=").append(upper)
                       .append(": {").append(upper).append("};\n");
            }
            if (lowerRate < 0) {
                content.append("\t\t").append(smvVarName).append("<=").append(lower)
                       .append(": {").append(lower).append("};\n");
            }

            StringBuilder rateSet = new StringBuilder("{");
            boolean first = true;
            if (lowerRate < 0) {
                rateSet.append(smvVarName).append(" - ").append(Math.abs(lowerRate));
                first = false;
            }
            if (!first) rateSet.append(", ");
            rateSet.append(smvVarName);
            if (upperRate > 0) {
                rateSet.append(", ").append(smvVarName).append(" + ").append(upperRate);
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
                content.append("\tesac;\n");
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
                content.append("\tesac;\n");
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
                    content.append("\tesac;\n");
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
                content.append("\n\tnext(").append(propVar).append(") := ").append(propVar).append(";\n");
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
     * 当前保持不变（无规则修改 content 隐私本身），预留扩展点。
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
                // IsChangeable=true 的 content 是 VAR，需要 next()
                String propVar = varName + ".privacy_" + ci.getName();
                content.append("\n\tnext(").append(propVar).append(") := ").append(propVar).append(";\n");
            }
        }
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
                                    String stateVarFallback = (smv.getModes() != null && smv.getModes().size() == 1) ? smv.getModes().get(0) : "state";
                                    content.append("\t\t").append(varName).append(".").append(stateVarFallback).append("=")
                                           .append(state.getName().replace(" ", "")).append(": ").append(dynamic.getChangeRate()).append(";\n");
                                }
                            }
                        }
                    }
                }

                content.append("\t\tTRUE: 0;\n");
                content.append("\tesac;\n");
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
                                    content.append(varName).append(".")
                                           .append(trigger.getAttribute()).append(" ")
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
                        content.append("\t\t").append(varRef).append(">=").append(var.getUpperBound())
                               .append(": ").append(var.getUpperBound()).append(";\n");
                    }
                    if (var.getLowerBound() != null && (lowerNcr < 0 || !impactedRate.isEmpty())) {
                        content.append("\t\t").append(varRef).append("<=").append(var.getLowerBound())
                               .append(": ").append(var.getLowerBound()).append(";\n");
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

                content.append("\tesac;\n");
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

    /**
     * 校验环境变量初始值是否在声明范围内。
     * 对于数值型变量，超出范围时 clamp 到边界并记录警告。
     * 对于枚举型变量，检查值是否在枚举列表中。
     */
    private String validateEnvVarInitValue(String varName, String userInit,
                                           DeviceManifest.InternalVariable var, boolean isAttack) {
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
                    upper = upper + Math.max(10, range / 5);
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
        return userInit;
    }

    /**
     * 判断某个属性名是否是任意设备声明的环境变量（IsInside=false）。
     */
    private boolean isEnvVariable(String attrName,
                                  List<DeviceVerificationDto> devices,
                                  Map<String, DeviceSmvData> deviceSmvMap) {
        if (attrName == null) return false;
        for (DeviceVerificationDto dev : devices) {
            DeviceSmvData smv = deviceSmvMap.get(dev.getVarName());
            if (smv != null && smv.getEnvVariables().containsKey(attrName)) {
                return true;
            }
        }
        return false;
    }

    /**
     * 将前端关系符（EQ/NEQ/GT/GTE/LT/LTE）归一化为 NuSMV 运算符。
     */
    private static String normalizeRuleRelation(String relation) {
        if (relation == null) return "=";
        return switch (relation.toUpperCase()) {
            case "EQ", "==" -> "=";
            case "NEQ", "!=" -> "!=";
            case "GT" -> ">";
            case "GTE" -> ">=";
            case "LT" -> "<";
            case "LTE" -> "<=";
            default -> relation;
        };
    }
}
