package cn.edu.nju.Iot_Verify.component.nusmv.generator.module;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.PropertyDimension;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvBoundsUtils;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvRelationUtils;
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

        // 閸欏倹鏆熸宀冪槈
        if (devices == null) {
            log.error("SmvMainModuleBuilder.build: devices 閸欏倹鏆熸稉宥堝厴娑撶皠ull");
            throw SmvGenerationException.invalidBuilderInput(
                    "SmvMainModuleBuilder",
                    "devices",
                    "must not be null");
        }
        if (deviceSmvMap == null) {
            log.error("SmvMainModuleBuilder.build: deviceSmvMap 閸欏倹鏆熸稉宥堝厴娑撶皠ull");
            throw SmvGenerationException.invalidBuilderInput(
                    "SmvMainModuleBuilder",
                    "deviceSmvMap",
                    "must not be null");
        }

        StringBuilder content = new StringBuilder();

        content.append("\nMODULE main");

        // intensity 閺勵垰鍠曠紒鎾冲綁闁插骏绱欐稉宥瓻DIC 娑撯偓閼疯揪绱氶敍姘偓鑲╂暠閸氬嫯顔曟径鍣剆_attack 娑斿鎷伴崘鍐茬暰閿涘矂鐛欑拠浣界箖缁嬪鑵戞稉宥呭綁
        // 閸欘亣顩?isAttack=true 鐏忓崬锛愰弰宸宯tensity閿涘苯鑻熼悽鈫朜VAR 缁撅附娼稉濠囨
        // Attack-mode guard.
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
        // Collect env var user-provided init values: varName -> deviceVarName -> validatedInit.
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
                        int upper = SmvBoundsUtils.resolveEffectiveUpperBound(lower, var.getUpperBound(), isAttack, intensity);
                        content.append(lower).append("..").append(upper).append(";");
                    } else {
                        // NuSMV has no "integer" type; use a safe default range.
                        content.append("0..100;");
                    }
                }
                // Record each device-provided init value for same-name env-var conflict checks.
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

        // 閻㈢喐鍨氶悳顖氼暔閸欐﹢鍣洪惃鍒琻it()閿涘牅濞囬悽銊ф暏閹撮攱瀵氱€规氨娈戦崚婵嗩潗閸婄》绱?
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
        appendEnvTransitions(content, devices, deviceSmvMap, isAttack, intensity);
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
        appendInternalVariableTransitions(content, devices, deviceSmvMap, isAttack, intensity);

        return content.toString();
    }

    /**
     * 娑撶儤澧嶉張澶庮啎婢跺洨娈?IsInside=false 閸欐﹢鍣洪悽鐔稿灇缁犫偓閸楁洝绁撮崐纭风礄闂€婊冨剼閻滎垰顣ㄩ崣姗€鍣洪敍澶涙嫹?     * 娓氬顩ч敍姝礹ermostat.temperature := a_temperature;
     * 娑撳秹妾烘禍搴濈炊閹扮喎娅掔拋鎯ь槵閳ユ柡鈧棃娼导鐘冲妳閸ｃ劏顔曟径鍥风礄婵′繂hermostat閿涘娈戞径鏍劥閸欐﹢鍣烘稊鐔兼付鐟曚浇绻涢幒銉ュ煂閻滎垰顣ㄩ崣姗€鍣洪敓?     */
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

    private Map<String, List<RuleDto>> groupRulesByResolvedTarget(List<RuleDto> rules,
                                                                   Map<String, DeviceSmvData> deviceSmvMap) {
        Map<String, List<RuleDto>> rulesByTarget = new LinkedHashMap<>();
        if (rules == null) {
            return rulesByTarget;
        }
        for (RuleDto rule : rules) {
            if (rule == null || rule.getCommand() == null) {
                continue;
            }
            String requestedTarget = rule.getCommand().getDeviceName();
            if (requestedTarget == null || requestedTarget.isBlank()) {
                continue;
            }
            DeviceSmvData targetSmv = DeviceSmvDataFactory.findDeviceSmvDataStrict(requestedTarget, deviceSmvMap);
            if (targetSmv == null) {
                throw SmvGenerationException.deviceNotFound(requestedTarget);
            }
            rulesByTarget.computeIfAbsent(targetSmv.getVarName(), k -> new ArrayList<>()).add(rule);
        }
        return rulesByTarget;
    }

    private void appendStateTransitions(StringBuilder content,
                                       List<DeviceVerificationDto> devices,
                                       List<RuleDto> rules,
                                       Map<String, DeviceSmvData> deviceSmvMap,
                                       boolean isAttack) {
        Map<String, List<RuleDto>> rulesByTarget = groupRulesByResolvedTarget(rules, deviceSmvMap);

        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.getModes() == null) continue;

            String varName = smv.getVarName();
            List<RuleDto> deviceRules = rulesByTarget.get(varName);

            if (!smv.getModes().isEmpty()) {
                for (int modeIdx = 0; modeIdx < smv.getModes().size(); modeIdx++) {
                    String mode = smv.getModes().get(modeIdx);
                    List<String> modeStates = smv.getModeStates().get(mode);
                    if (modeStates == null || modeStates.isEmpty()) continue;

                    content.append("\n\tnext(").append(varName).append(".").append(mode).append(") :=\n");
                    content.append("\tcase\n");

                    // In attack mode, actuator state can be hijacked to any legal state.
                    if (isAttack && !smv.isSensor()) {
                        content.append("\t\t").append(varName).append(".is_attack=TRUE: {")
                               .append(String.join(", ", modeStates)).append("};\n");
                    }

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
                            appendRuleConditions(content, rule, deviceSmvMap, true, varName);

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
                                // M4 娣囶喖顦查敍姝祌igger value 闂団偓鐟曚礁骞撶粚鐑樼壐
                                String triggerValue = trigger.getValue() != null ? trigger.getValue().replace(" ", "") : "";
                                String triggerRelation = normalizeTriggerRelationOrThrow(
                                        smv.getVarName(), "Transition '" + trans.getName() + "'", trigger.getRelation());
                                String startState = getStateForMode(trans.getStartState(), modeIdx);

                                content.append("\t\t");
                                if (startState != null && !startState.isEmpty()) {
                                    content.append(varName).append(".").append(mode).append("=").append(startState).append(" & ");
                                }
                                content.append(varName).append(".")
                                       .append(trigger.getAttribute())
                                       .append(triggerRelation)
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

    private void appendRuleConditions(StringBuilder content, RuleDto rule, Map<String, DeviceSmvData> deviceSmvMap, boolean useNext) {
        appendRuleConditions(content, rule, deviceSmvMap, useNext, null);
    }

    private void appendRuleConditions(StringBuilder content, RuleDto rule, Map<String, DeviceSmvData> deviceSmvMap,
                                      boolean useNext, String transitionTargetVarName) {
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

            String part = buildSingleCondition(condition, deviceSmvMap, useNext, transitionTargetVarName);
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


    private String buildSingleCondition(RuleDto.Condition condition, Map<String, DeviceSmvData> deviceSmvMap,
                                        boolean useNext, String transitionTargetVarName) {
        String deviceId = condition.getDeviceName();
        DeviceSmvData condSmv = DeviceSmvDataFactory.findDeviceSmvDataStrict(deviceId, deviceSmvMap);

        if (condSmv == null) {
            log.warn("Rule condition references unknown device '{}' and cannot be resolved", deviceId);
            return null;
        }

        String varName = condSmv.getVarName();
        boolean effectiveUseNext = useNext;
        if (useNext && transitionTargetVarName != null && transitionTargetVarName.equals(varName)) {
            // Avoid recursively defined next(target.*) when target rules read target state/vars.
            effectiveUseNext = false;
        }
        String attr = condition.getAttribute();
        if (attr == null || attr.isBlank()) {
            log.warn("Rule condition has null/blank attribute for device '{}' and cannot be resolved", deviceId);
            return null;
        }

        if (condition.getRelation() != null) {
            if (condition.getValue() == null || condition.getValue().isBlank()) {
                log.warn("Rule condition has relation '{}' but null/blank value for device '{}' and cannot be resolved",
                        condition.getRelation(), deviceId);
                return null;
            }
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
            if ("state".equals(attr)) {
                return buildRuleStateCondition(condition, condSmv, normalizedRel, effectiveUseNext);
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
            String lhsExpr = varName + "." + lhsAttr;
            if (effectiveUseNext) {
                lhsExpr = "next(" + lhsExpr + ")";
            }
            String expr = buildRuleRelationExpr(lhsExpr, normalizedRel, rhsValue);
            if (expr == null || expr.isBlank()) {
                log.warn("Rule condition failed to build relation expression for device '{}' attribute '{}'", deviceId, attr);
                return null;
            }
            return expr;
        }

        DeviceManifest manifest = condSmv.getManifest();
        if (manifest == null || manifest.getApis() == null) return null;

        for (DeviceManifest.API api : manifest.getApis()) {
            if (!Boolean.TRUE.equals(api.getSignal()) || !api.getName().equals(condition.getAttribute())) {
                continue;
            }

            String apiSignal = DeviceSmvDataFactory.formatApiSignalName(api.getName());
            String apiSignalExpr = null;
            if (apiSignal != null) {
                String apiSignalLhs = varName + "." + apiSignal;
                if (effectiveUseNext) {
                    apiSignalLhs = "next(" + apiSignalLhs + ")";
                }
                apiSignalExpr = apiSignalLhs + "=TRUE";
            }

            String endState = api.getEndState();
            if (endState != null && condSmv.getModes() != null && !condSmv.getModes().isEmpty()) {
                int modeIdx = DeviceSmvDataFactory.getModeIndexOfState(condSmv, endState);
                if (modeIdx >= 0 && modeIdx < condSmv.getModes().size()) {
                    String mode = condSmv.getModes().get(modeIdx);
                    String cleanEndState = getStateForMode(endState, modeIdx);
                    if (cleanEndState != null && !cleanEndState.isEmpty()) {
                        String stateLhs = varName + "." + mode;
                        if (effectiveUseNext) {
                            stateLhs = "next(" + stateLhs + ")";
                        }
                        String stateExpr = stateLhs + "=" + cleanEndState;
                        return apiSignalExpr != null
                                ? "(" + apiSignalExpr + " | " + stateExpr + ")"
                                : stateExpr;
                    }
                }
            }

            if (apiSignalExpr != null) {
                return apiSignalExpr;
            }
            break;
        }
        log.warn("Rule condition: attribute '{}' on device '{}' did not match any mode, variable, or API signal",
                condition.getAttribute(), deviceId);
        return null;
    }
private String buildRuleStateCondition(RuleDto.Condition condition, DeviceSmvData condSmv,
                                           String normalizedRel, boolean useNext) {
        String deviceId = condition.getDeviceName();
        if (condSmv.getModes() == null || condSmv.getModes().isEmpty()) {
            log.warn("Rule state condition references no-mode device '{}' and cannot be resolved", deviceId);
            return null;
        }
        if (!"=".equals(normalizedRel)
                && !"!=".equals(normalizedRel)
                && !"in".equals(normalizedRel)
                && !"not in".equals(normalizedRel)) {
            log.warn("Rule state condition relation '{}' is not supported for device '{}'", normalizedRel, deviceId);
            return null;
        }

        List<String> rawCandidates = splitStateRuleCandidates(condition.getValue(), normalizedRel, condSmv);
        if (rawCandidates.isEmpty()) {
            log.warn("Rule state condition has empty candidate set on device '{}'", deviceId);
            return null;
        }

        List<String> tupleExprs = new ArrayList<>();
        for (String rawCandidate : rawCandidates) {
            Map<String, String> modeStateMap = resolveStateTupleCandidate(condSmv, rawCandidate);
            if (modeStateMap == null || modeStateMap.isEmpty()) {
                log.warn("Rule state condition value '{}' on device '{}' cannot be resolved to a legal mode tuple",
                        rawCandidate, deviceId);
                return null;
            }
            String tupleExpr = buildStateTupleExpr(condSmv.getVarName(), condSmv, modeStateMap, useNext);
            if (tupleExpr == null || tupleExpr.isBlank()) {
                log.warn("Rule state condition tuple '{}' on device '{}' produced no expression", rawCandidate, deviceId);
                return null;
            }
            tupleExprs.add(tupleExpr);
        }

        if ("=".equals(normalizedRel)) {
            if (tupleExprs.size() != 1) {
                log.warn("Rule state '=' condition on device '{}' resolved to multiple candidates: {}", deviceId, rawCandidates);
                return null;
            }
            return tupleExprs.get(0);
        }
        if ("!=".equals(normalizedRel)) {
            if (tupleExprs.size() != 1) {
                log.warn("Rule state '!=' condition on device '{}' resolved to multiple candidates: {}", deviceId, rawCandidates);
                return null;
            }
            return "!(" + tupleExprs.get(0) + ")";
        }
        if ("in".equals(normalizedRel)) {
            return tupleExprs.size() == 1 ? tupleExprs.get(0) : "(" + String.join(" | ", tupleExprs) + ")";
        }

        List<String> negated = new ArrayList<>();
        for (String tupleExpr : tupleExprs) {
            negated.add("!(" + tupleExpr + ")");
        }
        return negated.size() == 1 ? negated.get(0) : "(" + String.join(" & ", negated) + ")";
    }

    private List<String> splitStateRuleCandidates(String value, String normalizedRel, DeviceSmvData condSmv) {
        if (value == null) {
            return List.of();
        }
        if ("in".equals(normalizedRel) || "not in".equals(normalizedRel)) {
            String splitRegex = (condSmv.getModes() != null && condSmv.getModes().size() > 1) ? "[,|]" : "[,;|]";
            String[] parts = value.split(splitRegex);
            List<String> result = new ArrayList<>();
            for (String part : parts) {
                String trimmed = part.trim();
                if (!trimmed.isEmpty()) {
                    result.add(trimmed);
                }
            }
            return result;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty() ? List.of() : List.of(trimmed);
    }

    private Map<String, String> resolveStateTupleCandidate(DeviceSmvData condSmv, String rawCandidate) {
        if (condSmv == null || condSmv.getModes() == null || condSmv.getModes().isEmpty()
                || rawCandidate == null || rawCandidate.isBlank()) {
            return null;
        }

        List<String> modes = condSmv.getModes();
        String candidate = rawCandidate.trim();

        if (candidate.contains(";")) {
            String[] segments = candidate.split(";", -1);
            if (segments.length != modes.size()) {
                return null;
            }
            Map<String, String> tuple = new LinkedHashMap<>();
            for (int i = 0; i < modes.size(); i++) {
                String cleanSeg = DeviceSmvDataFactory.cleanStateName(segments[i]);
                if (cleanSeg == null || cleanSeg.isBlank()) {
                    continue;
                }
                String mode = modes.get(i);
                List<String> legalStates = condSmv.getModeStates().get(mode);
                if (legalStates == null || !legalStates.contains(cleanSeg)) {
                    return null;
                }
                tuple.put(mode, cleanSeg);
            }
            return tuple.isEmpty() ? null : tuple;
        }

        String cleanState = DeviceSmvDataFactory.cleanStateName(candidate);
        if (cleanState == null || cleanState.isBlank()) {
            return null;
        }

        if (modes.size() == 1) {
            String mode = modes.get(0);
            List<String> legalStates = condSmv.getModeStates().get(mode);
            if (legalStates == null || !legalStates.contains(cleanState)) {
                return null;
            }
            Map<String, String> tuple = new LinkedHashMap<>();
            tuple.put(mode, cleanState);
            return tuple;
        }

        List<String> matchedModes = new ArrayList<>();
        for (String mode : modes) {
            List<String> legalStates = condSmv.getModeStates().get(mode);
            if (legalStates != null && legalStates.contains(cleanState)) {
                matchedModes.add(mode);
            }
        }
        if (matchedModes.size() != 1) {
            return null;
        }
        Map<String, String> tuple = new LinkedHashMap<>();
        tuple.put(matchedModes.get(0), cleanState);
        return tuple;
    }

    private String buildStateTupleExpr(String varName, DeviceSmvData condSmv,
                                       Map<String, String> modeStateMap, boolean useNext) {
        List<String> parts = new ArrayList<>();
        for (String mode : condSmv.getModes()) {
            String state = modeStateMap.get(mode);
            if (state == null || state.isBlank()) {
                continue;
            }
            String lhs = varName + "." + mode;
            if (useNext) {
                lhs = "next(" + lhs + ")";
            }
            parts.add(lhs + "=" + state);
        }
        if (parts.isEmpty()) {
            return null;
        }
        return parts.size() == 1 ? parts.get(0) : "(" + String.join(" & ", parts) + ")";
    }

    private void appendEnvTransitions(StringBuilder content,
                                     List<DeviceVerificationDto> devices,
                                     Map<String, DeviceSmvData> deviceSmvMap,
                                     boolean isAttack,
                                     int intensity) {

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
                                    // P4: 閼活櫤rigger.attribute 閺堫剝闊╅弰鐥歯v var閿涘瞼娲块幒銉ф暏 a_<attr>
                                    String triggerRelation = normalizeTriggerRelationOrThrow(
                                            transSmv.getVarName(), "Transition '" + trans.getName() + "'", trigger.getRelation());
                                    String triggerRef;
                                    if (transSmv.getEnvVariables().containsKey(trigger.getAttribute())) {
                                        triggerRef = "a_" + trigger.getAttribute();
                                    } else {
                                        triggerRef = transSmv.getVarName() + "." + trigger.getAttribute();
                                    }
                                    content.append("\t\t");
                                    // P1-1 娣囶喖顦查敍姘杻閸旂垙tartState 缁撅附娼?
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
                                           .append(triggerRelation).append(" ")
                                           .append(trigger.getValue().replace(" ", "")).append(": ").append(assignment.getValue().replace(" ", "")).append(";\n");
                                }
                            }
                        }
                    }
                }

                if (var.getValues() != null && !var.getValues().isEmpty()) {
                    // 閺嬫矮濡囬崹瀣箚婢у啫褰夐柌蹇ョ窗闂堢偟鈥樼€规碍鈧団偓澶嬪閹碘偓閺堝褰查懗钘夆偓纭风礄娑撳窏ample.smv 娑撯偓閼疯揪绱?
                    List<String> cleanValues = new ArrayList<>();
                    for (String v : var.getValues()) {
                        cleanValues.add(v.replace(" ", ""));
                    }
                    content.append("\t\tTRUE: {").append(String.join(", ", cleanValues)).append("};\n");
                } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                    // Numeric environment variable transition with natural change and impacted rates.
                    appendNumericEnvTransition(content, smvVarName, var, varName, devices, deviceSmvMap, isAttack, intensity);
                } else {
                    content.append("\t\tTRUE: ").append(smvVarName).append(";\n");
                }

                content.append("\tesac;");
            }
        }
    }

    /**
     * 閻㈢喐鍨氶弫鏉库偓鐓庣€烽悳顖氼暔閸欐﹢鍣洪惃鍒礶xt() 鏉烆剚宕查敍灞藉棘閻擃湽ample.smv 閺嶇厧绱￠敓?     * 閸栧懎鎯堢拋鎯ь槵瑜板崬鎼烽悳鍥风礄婵′繘irconditioner.temperature_rate閿涘鎷?NaturalChangeRate
     */
    private void appendNumericEnvTransition(StringBuilder content, String smvVarName,
                                            DeviceManifest.InternalVariable var, String varName,
                                            List<DeviceVerificationDto> devices,
                                            Map<String, DeviceSmvData> deviceSmvMap,
                                            boolean isAttack,
                                            int intensity) {
        int lower = var.getLowerBound();
        int upper = SmvBoundsUtils.resolveEffectiveUpperBound(lower, var.getUpperBound(), isAttack, intensity);

        int[] ncr = parseNaturalChangeRate(var.getNaturalChangeRate(), "env:" + varName);
        int lowerRate = ncr[0], upperRate = ncr[1];

        // 閿熸枻鎷烽敓鏂ゆ嫹閿熸枻鎷烽敓鏂ゆ嫹褰遍敓鏂ゆ嫹鍚敓鏂ゆ嫹閿熸枻鎷烽敓鏂ゆ嫹鐠為潻鎷烽敓?rate 閿熸枻鎷烽敓鏂ゆ嫹
        String rateExpr = findImpactRateExpression(varName, devices, deviceSmvMap);

        if (rateExpr != null) {
            // Impacted-rate branch: clamp every candidate to the declared range.
            content.append("\t\t").append(smvVarName).append("=").append(upper)
                   .append("-(").append(rateExpr).append("): {")
                   .append(clampExpr("toint(" + smvVarName + ")-1+" + rateExpr, lower, upper))
                   .append(", ")
                   .append(clampExpr(smvVarName + "+" + rateExpr, lower, upper))
                   .append("};\n");

            content.append("\t\t").append(smvVarName).append(">").append(upper)
                   .append("-(").append(rateExpr).append("): {").append(upper).append("};\n");

            content.append("\t\t").append(smvVarName).append("=").append(lower)
                   .append("-(").append(rateExpr).append("): {")
                   .append(clampExpr(smvVarName + "+" + rateExpr, lower, upper))
                   .append(", ")
                   .append(clampExpr(smvVarName + "+1+" + rateExpr, lower, upper))
                   .append("};\n");

            content.append("\t\t").append(smvVarName).append("<").append(lower)
                   .append("-(").append(rateExpr).append("): {").append(lower).append("};\n");

            List<String> rateCandidates = new ArrayList<>();
            if (lowerRate != 0) {
                rateCandidates.add(clampExpr(formatArithmeticExpr(smvVarName, lowerRate) + "+" + rateExpr, lower, upper));
            }
            rateCandidates.add(clampExpr(smvVarName + "+" + rateExpr, lower, upper));
            if (upperRate != 0) {
                rateCandidates.add(clampExpr(formatArithmeticExpr(smvVarName, upperRate) + "+" + rateExpr, lower, upper));
            }
            content.append("\t\tTRUE: {").append(String.join(", ", rateCandidates)).append("};\n");
        } else {
            // 閿熸枻鎷烽敓鍊熷褰遍敓鏂ゆ嫹閿熺粸锝忔嫹NaturalChangeRate閿熸枻鎷稵RUE 閿熸枻鎷锋敮閿熸枻鎷烽€夊€煎悓閿熸枻鎷烽敓鍙枻鎷?
            if (upperRate > 0) {
                StringBuilder upperSet = new StringBuilder("{");
                if (lowerRate < 0) {
                    upperSet.append(clampExpr(formatArithmeticExpr(smvVarName, lowerRate), lower, upper)).append(", ");
                }
                upperSet.append(smvVarName).append("}");
                content.append("\t\t").append(smvVarName).append(">=").append(upper)
                       .append(": ").append(upperSet).append(";\n");
            }
            if (lowerRate < 0) {
                StringBuilder lowerSet = new StringBuilder("{").append(smvVarName);
                if (upperRate > 0) {
                    lowerSet.append(", ").append(clampExpr(formatArithmeticExpr(smvVarName, upperRate), lower, upper));
                }
                lowerSet.append("}");
                content.append("\t\t").append(smvVarName).append("<=").append(lower)
                       .append(": ").append(lowerSet).append(";\n");
            }

            List<String> rateCandidates = new ArrayList<>();
            if (lowerRate < 0) {
                rateCandidates.add(clampExpr(formatArithmeticExpr(smvVarName, lowerRate), lower, upper));
            }
            rateCandidates.add(clampExpr(smvVarName, lower, upper));
            if (upperRate > 0) {
                rateCandidates.add(clampExpr(formatArithmeticExpr(smvVarName, upperRate), lower, upper));
            }
            content.append("\t\tTRUE: {").append(String.join(", ", rateCandidates)).append("};\n");
        }
    }

    /**
     * Find all device rate expressions that impact the target variable.
     * Example: "air_conditioner.temperature_rate"
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
        // Multiple devices affecting the same variable are summed.
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
                } else if (smv.getModes() != null && smv.getModes().size() == 1) {
                    String stateVar = smv.getModes().get(0);
                    String cleanEnd = DeviceSmvDataFactory.cleanStateName(endState);
                    String cleanStart = (startState != null) ? DeviceSmvDataFactory.cleanStateName(startState) : "";
                    if (cleanEnd == null || cleanEnd.isEmpty()) {
                        log.warn("API signal '{}' on device '{}' has empty endState and cannot derive transition pulse",
                                api.getName(), varName);
                    } else if (cleanStart.isEmpty()) {
                        content.append("\t\t").append(varName).append(".").append(stateVar).append("!=").append(cleanEnd)
                               .append(" & next(").append(varName).append(".").append(stateVar).append(")=").append(cleanEnd).append(": TRUE;\n");
                    } else {
                        content.append("\t\t").append(varName).append(".").append(stateVar).append("=").append(cleanStart)
                               .append(" & next(").append(varName).append(".").append(stateVar).append(")=").append(cleanEnd).append(": TRUE;\n");
                    }
                } else {
                    log.warn("API signal '{}' on no-mode device '{}' cannot derive state-based pulse; defaulting to FALSE",
                            api.getName(), varName);
                }

                content.append("\t\tTRUE: FALSE;\n");
                content.append("\tesac;");
            }
        }
    }

    /**
     * 娑撶皪ransition signal閿涘牓娼?API signal閿涘鏁撻幋鎭榚xt() 鏉烆剚宕查敓?     * 瑜版捁顔曟径鍥︾矤 startState 鏉烆剚宕查崚鐧硁dState 閺冪ignal=TRUE閿涘苯鎯侀崚姗LSE閿?     */
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

        Map<String, List<RuleDto>> rulesByTarget = groupRulesByResolvedTarget(rules, deviceSmvMap);

        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.isSensor()) continue;

            String varName = smv.getVarName();
            List<RuleDto> deviceRules = rulesByTarget.get(varName);

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
                                appendRuleConditions(content, rule, deviceSmvMap, false);
                                content.append(" & (");
                                appendRulePropertyConditions(content, rule, deviceSmvMap, dim);
                                // content 闂呮劗顫嗘导鐘虫尡閿涙俺顫夐崚娆愭儭鐢泬ontentDevice.content 閺冩儼鎷烽崝鐕緊ntent privacy 閺夆€叉
                                if (dim == PropertyDimension.PRIVACY) {
                                    String contentCond = buildContentPrivacyCondition(rule, deviceSmvMap);
                                    if (contentCond != null) {
                                        content.append(" | ").append(contentCond);
                                    }
                                }
                                content.append("): ").append(dim.activeValue).append(";\n");

                                if (dim == PropertyDimension.TRUST) {
                                    content.append("\t\t");
                                    appendRuleConditions(content, rule, deviceSmvMap, false);
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
     * 娑撶ctuator 鐠佹儳顦惃鍕綁闁插繒楠?trust/privacy 閻㈢喐鍨?next() 鏉烆剚宕查敍鍫ｅ殰娣囨繃瀵旈敍澶涙嫹?     * 鏉╂瑤绨洪崣姗€鍣洪崷鈯縨vDeviceModuleBuilder 娑擃厼锛愰弰搴濊礋 VAR閿涘苯绻€妞ょ粯婀?next() 閸氾箑鍨?NuSMV 鐟欏棔璐熼棃鐐碘€樼€规碍鈧嶆嫹?     */
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
            DeviceSmvData condSmv = DeviceSmvDataFactory.findDeviceSmvDataStrict(condition.getDeviceName(), deviceSmvMap);
            if (condSmv == null || condSmv.getManifest() == null) continue;

            String part = buildPropertyConditionPart(condition, condSmv, condSmv.getVarName(), condSmv.getManifest(), dim);
            if (part != null && !part.isEmpty()) parts.add(part);
        }

        // C2 娣囶喖顦查敍姘閺堝娼禒鑸电爱闁棄褰叉穱鈩冩閹靛秳绱堕幘鐠絩usted閿涘瞼鏁?& 閼板矂娼?|
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
                    // First check whether attribute is a mode name.
                    if (condSmv.getModes().contains(condition.getAttribute())) {
                        return condVarName + "." + dim.prefix + condition.getAttribute() + "_" + stateValue + "=" + dim.activeValue;
                    }
                    // Multi-mode value with semicolons should be mapped segment by segment.
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
                    // 閸氾箑鍨幐濉縜lue 閸︺劌鎽㈡稉鐚皁de 閻ㄥ嫮濮搁幀浣稿灙鐞涖劋鑵戦弻銉﹀
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
     * 瑜版捁顫夐崚娆忔嚒娴犮倖鎯＄敮顩塷ntentDevice.content 閺冭绱濋悽鐔稿灇 content 闂呮劗顫嗛弶鈥叉閿?     * 娓氬顩х憴鍕灟 "THEN Facebook.post(MobilePhone.photo)" 閿?mobilephone.privacy_photo=private"
     */
    private String buildContentPrivacyCondition(RuleDto rule, Map<String, DeviceSmvData> deviceSmvMap) {
        if (rule.getCommand() == null) return null;
        String contentDevice = rule.getCommand().getContentDevice();
        String contentName = rule.getCommand().getContent();
        if (contentDevice == null || contentDevice.isBlank() || contentName == null || contentName.isBlank()) return null;

        DeviceSmvData contentSmv = DeviceSmvDataFactory.findDeviceSmvDataStrict(contentDevice, deviceSmvMap);
        if (contentSmv == null) {
            throw SmvGenerationException.deviceNotFound(contentDevice);
        }
        if (contentSmv.getContents() == null) {
            return null;
        }

        // 妤犲矁鐦?content 绾喖鐤勭€涙ê婀禍搴ゎ嚉鐠佹儳顦?
        for (DeviceSmvData.ContentInfo ci : contentSmv.getContents()) {
            if (contentName.equals(ci.getName())) {
                return contentSmv.getVarName() + ".privacy_" + contentName + "=private";
            }
        }
        return null;
    }

    /**
     * 娑撶瘨sChangeable=true 閻ㄥ垻ontent 閻㈢喐鍨?next() 鏉烆剚宕查敓?     * 瑜版捁顫夐崚娆忔嚒娴犮倕绱╅悽銊ょ啊鐠囶櫓ontent閿涘牆顩?THEN Facebook.post(MobilePhone.photo)閿涘妞傞敓?     * 鐟欏嫬鍨憴锕€褰傛导姘殺 content 闂呮劗顫嗙拋鍙ヨ礋 private閿涙稑鎯侀崚娆掑殰娣囨繃瀵旈敓?     */
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

                // Collect rules that reference this content variable.
                List<RuleDto> matchingRules = findRulesReferencingContent(
                        rules, device.getVarName(), ci.getName(), deviceSmvMap);

                if (matchingRules.isEmpty()) {
                    // No matching rule: keep current value.
                    content.append("\n\tnext(").append(propVar).append(") := ").append(propVar).append(";");
                } else {
                    content.append("\n\tnext(").append(propVar).append(") :=\n");
                    content.append("\tcase\n");
                    for (RuleDto rule : matchingRules) {
                        content.append("\t\t");
                        appendRuleConditions(content, rule, deviceSmvMap, false);
                        content.append(": private;\n");
                    }
                    content.append("\t\tTRUE: ").append(propVar).append(";\n");
                    content.append("\tesac;");
                }
            }
        }
    }

    /**
     * 閺屻儲澹橀幍鈧張濉﹐mmand.contentDevice 閸栧綊鍘ら幐鍥х暰鐠佹儳顦稉鏀僶mmand.content 閸栧綊鍘ら幐鍥х暰 content 閸氬秶袨閻ㄥ嫯顫夐崚娆欐嫹?     */
    private List<RuleDto> findRulesReferencingContent(List<RuleDto> rules,
                                                       String deviceVarName,
                                                       String contentName,
                                                       Map<String, DeviceSmvData> deviceSmvMap) {
        List<RuleDto> result = new ArrayList<>();
        if (rules == null) return result;
        for (RuleDto rule : rules) {
            if (rule == null || rule.getCommand() == null) continue;
            String cd = rule.getCommand().getContentDevice();
            String cn = rule.getCommand().getContent();
            if (cn == null || !cn.equals(contentName)) continue;
            if (cd == null || cd.isBlank()) continue;
            DeviceSmvData contentSmv = DeviceSmvDataFactory.findDeviceSmvDataStrict(cd, deviceSmvMap);
            if (contentSmv == null) {
                throw SmvGenerationException.deviceNotFound(cd);
            }
            if (deviceVarName.equals(contentSmv.getVarName())) {
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
                                    boolean firstCond = true;
                                    for (int c = 0; c < smv.getModes().size() && c < states.length; c++) {
                                        String rawSeg = states[c].trim();
                                        if (rawSeg.isEmpty()) continue;
                                        if (firstCond) {
                                            content.append("\t\t");
                                        } else {
                                            content.append(" & ");
                                        }
                                        firstCond = false;
                                        content.append(varName).append(".").append(smv.getModes().get(c))
                                               .append("=").append(DeviceSmvDataFactory.cleanStateName(rawSeg));
                                    }
                                    if (firstCond) continue; // all segments empty 閿?skip this CASE branch
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
                                                  boolean isAttack,
                                                  int intensity) {
        for (DeviceVerificationDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
            if (smv == null || smv.getManifest() == null || smv.getManifest().getInternalVariables() == null) continue;

            String varName = smv.getVarName();
            boolean isSensor = smv.isSensor();

            for (DeviceManifest.InternalVariable var : smv.getManifest().getInternalVariables()) {
                if (var.getIsInside() == null || !var.getIsInside()) {
                    continue;
                }

                Integer lowerBound = var.getLowerBound();
                Integer upperBound = var.getUpperBound();
                boolean hasNumericBounds = lowerBound != null && upperBound != null;
                if (hasNumericBounds && isAttack && isSensor) {
                    upperBound = SmvBoundsUtils.resolveEffectiveUpperBound(lowerBound, upperBound, true, intensity);
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
                    } else if (hasNumericBounds) {
                        content.append(lowerBound).append("..").append(upperBound).append(";\n");
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
                                    if (trans.getStartState() != null && smv.getModes() != null && !smv.getModes().isEmpty()) {
                                        for (int mi = 0; mi < smv.getModes().size(); mi++) {
                                            String ss = getStateForMode(trans.getStartState(), mi);
                                            if (ss != null && !ss.isEmpty()) {
                                                content.append(varName).append(".").append(smv.getModes().get(mi))
                                                       .append("=").append(ss).append(" & ");
                                            }
                                        }
                                    }
                                    String triggerRelation = normalizeTriggerRelationOrThrow(
                                            smv.getVarName(), "Transition '" + trans.getName() + "'", trigger.getRelation());
                                    String triggerRef;
                                    if (smv.getEnvVariables().containsKey(trigger.getAttribute())) {
                                        triggerRef = "a_" + trigger.getAttribute();
                                    } else {
                                        triggerRef = varName + "." + trigger.getAttribute();
                                    }
                                    content.append(triggerRef).append(" ")
                                           .append(triggerRelation).append(" ")
                                           .append(trigger.getValue().replace(" ", "")).append(": ")
                                           .append(assignment.getValue().replace(" ", "")).append(";\n");
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

                    if (upperBound != null && (upperNcr > 0 || !impactedRate.isEmpty())) {
                        if (impactedRate.isEmpty()) {
                            StringBuilder upperSet = new StringBuilder("{");
                            if (lowerNcr < 0) {
                                String expr = formatArithmeticExpr(varRef, lowerNcr);
                                upperSet.append(lowerBound != null ? clampExpr(expr, lowerBound, upperBound) : expr).append(", ");
                            }
                            upperSet.append(varRef).append("}");
                            content.append("\t\t").append(varRef).append(">=").append(upperBound)
                                   .append(": ").append(upperSet).append(";\n");
                        } else {
                            content.append("\t\t").append(varRef).append(">=").append(upperBound)
                                   .append(": ").append(upperBound).append(";\n");
                        }
                    }
                    if (lowerBound != null && (lowerNcr < 0 || !impactedRate.isEmpty())) {
                        if (impactedRate.isEmpty()) {
                            StringBuilder lowerSet = new StringBuilder("{").append(varRef);
                            if (upperNcr > 0) {
                                String expr = formatArithmeticExpr(varRef, upperNcr);
                                lowerSet.append(", ").append(upperBound != null ? clampExpr(expr, lowerBound, upperBound) : expr);
                            }
                            lowerSet.append("}");
                            content.append("\t\t").append(varRef).append("<=").append(lowerBound)
                                   .append(": ").append(lowerSet).append(";\n");
                        } else {
                            content.append("\t\t").append(varRef).append("<=").append(lowerBound)
                                   .append(": ").append(lowerBound).append(";\n");
                        }
                    }

                    List<String> rateCandidates = new ArrayList<>();
                    if (lowerNcr < 0) {
                        String lowerExpr = formatArithmeticExpr(varRef, lowerNcr);
                        if (!impactedRate.isEmpty()) {
                            lowerExpr = lowerExpr + "+" + impactedRate;
                        }
                        rateCandidates.add(hasNumericBounds ? clampExpr(lowerExpr, lowerBound, upperBound) : lowerExpr);
                    }
                    String steadyExpr = varRef;
                    if (!impactedRate.isEmpty()) {
                        steadyExpr = steadyExpr + "+" + impactedRate;
                    }
                    rateCandidates.add(hasNumericBounds ? clampExpr(steadyExpr, lowerBound, upperBound) : steadyExpr);
                    if (upperNcr > 0) {
                        String upperExpr = formatArithmeticExpr(varRef, upperNcr);
                        if (!impactedRate.isEmpty()) {
                            upperExpr = upperExpr + "+" + impactedRate;
                        }
                        rateCandidates.add(hasNumericBounds ? clampExpr(upperExpr, lowerBound, upperBound) : upperExpr);
                    }
                    content.append("\t\tTRUE: {").append(String.join(", ", rateCandidates)).append("};\n");
                } else {
                    if (smv.getManifest().getWorkingStates() != null) {
                        for (DeviceManifest.WorkingState state : smv.getManifest().getWorkingStates()) {
                            if (state.getDynamics() == null) continue;
                            for (DeviceManifest.Dynamic dynamic : state.getDynamics()) {
                                if (var.getName().equals(dynamic.getVariableName()) && dynamic.getValue() != null) {
                                    String cleanValue = dynamic.getValue().replace(" ", "");
                                    if (smv.getModes() != null && !smv.getModes().isEmpty()) {
                                        String[] stateNames = state.getName().split(";");
                                        boolean firstCond = true;
                                        for (int c = 0; c < smv.getModes().size() && c < stateNames.length; c++) {
                                            String rawSeg = stateNames[c].trim();
                                            if (rawSeg.isEmpty()) continue;
                                            if (firstCond) {
                                                content.append("\t\t");
                                            } else {
                                                content.append(" & ");
                                            }
                                            firstCond = false;
                                            content.append(varName).append(".").append(smv.getModes().get(c))
                                                   .append("=").append(DeviceSmvDataFactory.cleanStateName(rawSeg));
                                        }
                                        if (firstCond) continue;
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
     * Extract the state segment at modeIndex from a semicolon-separated state tuple.
     */
    private String getStateForMode(String multiModeState, int modeIndex) {
        if (multiModeState == null) return null;
        String[] states = multiModeState.split(";");
        if (modeIndex < states.length) {
            String raw = states[modeIndex].trim();
            if (raw.isEmpty()) return null;
            return DeviceSmvDataFactory.cleanStateName(raw);
        }
        return null;
    }

    private String formatArithmeticExpr(String varRef, int rate) {
        if (rate == 0) return varRef;
        if (rate > 0) return varRef + " + " + rate;
        return varRef + " - " + Math.abs(rate);
    }

    private String clampExpr(String expr, int lower, int upper) {
        return "max(" + lower + ", min(" + upper + ", " + expr + "))";
    }

    /**
     * 鐟欙絾鐎?NaturalChangeRate 鐎涙顑佹稉韫礋 [lowerRate, upperRate]閿?     * 閺嶇厧绱￠敍姘礋閿?3" 閹存牞瀵栭敓?[-1,2]"閿?     * 鏉╂柨娲?int[2]閿涘0]=lowerRate, [1]=upperRate閿?     */
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
     * 閺嶏繝鐛欓悳顖氼暔閸欐﹢鍣洪崚婵嗩潗閸婂吋妲搁崥锕€婀竟鐗堟閼煎啫娲块崘鍜冩嫹?     * 鐎甸€涚艾閺佹澘鈧厧鐎烽崣姗€鍣洪敍宀冪Т閸戦缚瀵栭崶瀛樻 clamp 閸掓媽绔熼悾灞借嫙鐠佹澘缍嶇拃锕€鎲￠敓?     * 鐎甸€涚艾閺嬫矮濡囬崹瀣綁闁插骏绱濆Λ鈧弻銉モ偓鍏兼Ц閸氾箑婀弸姘閸掓銆冩稉顓ㄦ嫹?     */
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
                int upper = SmvBoundsUtils.resolveEffectiveUpperBound(lower, var.getUpperBound(), isAttack, intensity);
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
        // 閺冪姵鐏囨稉鐐￥鏉堝湱鏅€规矮绠熼弮璁圭礉閸欐﹢鍣洪敓?main 娑擃厺浜?0..100 婢圭増妲戦敍灞藉灥閸婇棿绡冩惔鏂剧箽閹镐礁鎮撻懠鍐ㄦ纯閺佸瓨鏆?
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
     * 鐏忓棗澧犵粩顖氬彠缁崵顑佽ぐ鎺嶇閸栨牔璐?NuSMV 鏉╂劗鐣荤粭锔兼嫹?     */
    private String normalizeTriggerRelationOrThrow(String deviceName, String context, String rawRelation) {
        String normalized = SmvRelationUtils.normalizeTriggerRelation(rawRelation);
        if (!SmvRelationUtils.isSupportedTriggerRelation(normalized)) {
            throw SmvGenerationException.illegalTriggerRelation(
                    deviceName, context, rawRelation,
                    List.of("=", "!=", ">", ">=", "<", "<="));
        }
        return normalized;
    }

    private static String normalizeRuleRelation(String relation) {
        return SmvRelationUtils.normalizeRelation(relation);
    }

    private static boolean isSupportedRuleRelation(String relation) {
        return SmvRelationUtils.isSupportedRelation(relation);
    }

    /**
     * 鐏忓捄N/NOT_IN 鐏炴洖绱戞稉绡榰SMV 閿?x=a | x=b) 閿?x!=a & x!=b)閿?     * 闂堢偤娉﹂崥鍫ｇ箥缁犳顑侀惄瀛樺复鏉╂柨娲?left + relation + value閿?     */
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
     * 閿?;| 閹峰棗鍨庨崐鐓庡灙鐞涱煉绱欓悽銊ょ艾 IN/NOT_IN閿涘绱濋崡鏇炩偓鍏兼鏉╂柨娲栭崠鍛儓閸樼喎鈧偐娈戦崡鏇炲帗缁辩姴鍨悰顭掓嫹?     */
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
     * 鐎电ode 閻樿埖鈧礁鈧厧浠?cleanStateName閿涘瓥N/NOT_IN 閺冨爼鈧劒閲滃〒鍛倞閸愬秶鏁ら柅妤€褰块幏鍏煎复閿?     */
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
