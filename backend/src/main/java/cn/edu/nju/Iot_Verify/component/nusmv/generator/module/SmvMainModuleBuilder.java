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

        // Parameter validation
        if (devices == null) {
            log.error("SmvMainModuleBuilder.build: devices must not be null");
            throw SmvGenerationException.invalidBuilderInput(
                    "SmvMainModuleBuilder",
                    "devices",
                    "must not be null");
        }
        if (deviceSmvMap == null) {
            log.error("SmvMainModuleBuilder.build: deviceSmvMap must not be null");
            throw SmvGenerationException.invalidBuilderInput(
                    "SmvMainModuleBuilder",
                    "deviceSmvMap",
                    "must not be null");
        }

        StringBuilder content = new StringBuilder();

        content.append("\nMODULE main");

        // Attack-mode: intensity is declared as FROZENVAR with INVAR <= user-specified intensity;
        // is_attack boolean FROZENVAR is declared per device module.
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

        // Env variable init assignments
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
     * Assign external (IsInside=false) variables using simple assignment in main module.
     * e.g. Thermostat.temperature := a_temperature; The device module must not use init() for these.
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
                                // M4: clean trigger value (remove spaces for NuSMV compatibility)
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
                                    // P4: if trigger.attribute is an env var, reference it as a_<attr>
                                    String triggerRelation = normalizeTriggerRelationOrThrow(
                                            transSmv.getVarName(), "Transition '" + trans.getName() + "'", trigger.getRelation());
                                    String triggerRef;
                                    if (transSmv.getEnvVariables().containsKey(trigger.getAttribute())) {
                                        triggerRef = "a_" + trigger.getAttribute();
                                    } else {
                                        triggerRef = transSmv.getVarName() + "." + trigger.getAttribute();
                                    }
                                    content.append("\t\t");
                                    // P1-1: prepend StartState guard condition if present
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
                    // Enum env variable: non-deterministic choice from clean value set (consistent with sample.smv)
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
     * Generate numeric env variable next() transition following sample.smv pattern.
     * Incorporates device _rate (e.g. airconditioner.temperature_rate) and NaturalChangeRate.
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

        // Check if any device provides an impacted _rate expression for this variable
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
            // No impacted rate: use NaturalChangeRate for TRUE branch candidates
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
     * Generate Transition signal and API signal next() transitions.
     * When current state matches startState and next state matches endState, signal=TRUE; otherwise FALSE.
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
                                // Content privacy condition: check if rule references contentDevice.content for content privacy
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
     * Generate actuator internal variable trust/privacy next() transitions (keep current value).
     * These correspond to VAR declarations in SmvDeviceModuleBuilder; next() keeps value unchanged.
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

        int attemptedConditions = 0;
        List<String> parts = new ArrayList<>();
        for (RuleDto.Condition condition : rule.getConditions()) {
            if (condition == null || condition.getDeviceName() == null) continue;
            DeviceSmvData condSmv = DeviceSmvDataFactory.findDeviceSmvDataStrict(condition.getDeviceName(), deviceSmvMap);
            if (condSmv == null || condSmv.getManifest() == null) continue;
            attemptedConditions++;

            String part = buildPropertyConditionPart(condition, condSmv, condSmv.getVarName(), condSmv.getManifest(), dim);
            if (part != null && !part.isEmpty()) parts.add(part);
        }

        // C2: join trust/privacy condition parts with & (all sources must be trusted).
        // Fail-closed: if conditions existed but none produced a property part,
        // output FALSE rather than TRUE to avoid silently relaxing the property constraint.
        if (parts.isEmpty()) {
            if (attemptedConditions > 0) {
                log.warn("Rule has {} condition(s) but none produced a {} property part; using fail-closed FALSE",
                        attemptedConditions, dim.name());
                content.append("FALSE");
            } else {
                content.append("TRUE");
            }
        } else {
            content.append(String.join(" & ", parts));
        }
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

            String normalizedRel = normalizeRuleRelation(condition.getRelation());
            if (condition.getValue() != null && normalizedRel != null) {
                String stateValue = condition.getValue().replace(" ", "");

                if ("=".equals(normalizedRel)) {
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
                        // Try to match value to a mode's legal state list
                        for (String mode : condSmv.getModes()) {
                            List<String> modeStates = condSmv.getModeStates().get(mode);
                            if (modeStates != null && modeStates.contains(stateValue)) {
                                return condVarName + "." + dim.prefix + mode + "_" + stateValue + "=" + dim.activeValue;
                            }
                        }
                        log.warn("Trust/privacy propagation: state value '{}' not found in any mode for device '{}', skipping",
                                stateValue, condVarName);
                        return null;
                    } else {
                        return condVarName + "." + dim.prefix + stateValue + "=" + dim.activeValue;
                    }
                } else if ("!=".equals(normalizedRel)) {
                    // != on state: property-check all states EXCEPT stateValue.
                    // If attribute names a specific mode, scope to that mode only (consistent with = branch).
                    String targetMode = resolveAttributeAsMode(condSmv, condition);
                    return collectStatePropertyPartsExcluding(condSmv, condVarName, dim, Set.of(stateValue), targetMode);
                } else if ("in".equals(normalizedRel)) {
                    // IN: property-check each value in the set.
                    Set<String> values = parseStateValueSet(stateValue, condSmv);
                    String targetMode = resolveAttributeAsMode(condSmv, condition);
                    return collectStatePropertyPartsIncluding(condSmv, condVarName, dim, values, targetMode);
                } else if ("not in".equals(normalizedRel)) {
                    // NOT IN: property-check all states EXCEPT those in the set.
                    Set<String> values = parseStateValueSet(stateValue, condSmv);
                    String targetMode = resolveAttributeAsMode(condSmv, condition);
                    return collectStatePropertyPartsExcluding(condSmv, condVarName, dim, values, targetMode);
                }
                // For numeric comparisons (>, <, >=, <=) on enum states: fall through to null.
                // Caught by fail-closed check in appendRulePropertyConditions.
            }
        }
        return null;
    }

    /**
     * If condition.getAttribute() names one of the device's modes, return it as the target mode
     * for scoped property generation. Otherwise return null (process all modes).
     * Mirrors the attribute-is-mode check in the "=" branch of buildPropertyConditionPart.
     */
    private static String resolveAttributeAsMode(DeviceSmvData condSmv, RuleDto.Condition condition) {
        if (condSmv.getModes() != null && condition.getAttribute() != null
                && condSmv.getModes().contains(condition.getAttribute())) {
            return condition.getAttribute();
        }
        return null;
    }

    /**
     * Parse a state value set string (e.g. "A,B,C" or "[A|B|C]") into individual values.
     * Uses the same separator convention as splitStateRuleCandidates:
     * multi-mode devices use [,|] (preserving ; as tuple separator),
     * single-mode devices use [,;|].
     */
    private Set<String> parseStateValueSet(String raw, DeviceSmvData condSmv) {
        String cleaned = raw.replaceAll("[\\[\\]{}]", "");
        boolean multiMode = condSmv.getModes() != null && condSmv.getModes().size() > 1;
        String splitRegex = multiMode ? "[,|]" : "[,;|]";
        Set<String> result = new LinkedHashSet<>();
        for (String v : cleaned.split(splitRegex)) {
            String trimmed = v.trim().replace(" ", "");
            if (!trimmed.isEmpty()) result.add(trimmed);
        }
        return result;
    }

    /**
     * Collect property condition parts for states IN the given set.
     * Used for "IN" relation: ensure all listed states are trusted/private.
     * When targetMode is non-null, only considers states within that specific mode.
     * When targetMode is null, processes all modes and handles tuple values via resolveStateTupleCandidate.
     */
    private String collectStatePropertyPartsIncluding(DeviceSmvData condSmv, String condVarName,
                                                      PropertyDimension dim, Set<String> includeValues,
                                                      String targetMode) {
        List<String> propParts = new ArrayList<>();
        if (condSmv.getModes() != null && !condSmv.getModes().isEmpty()) {
            for (String val : includeValues) {
                if (targetMode != null) {
                    // Scoped to a single mode: match directly within that mode.
                    List<String> ms = condSmv.getModeStates() != null ? condSmv.getModeStates().get(targetMode) : null;
                    if (ms != null && ms.contains(val)) {
                        propParts.add(condVarName + "." + dim.prefix + targetMode + "_" + val + "=" + dim.activeValue);
                    }
                    continue;
                }
                // No target mode: try tuple resolution first, then simple match across modes.
                Map<String, String> tuple = resolveStateTupleCandidate(condSmv, val);
                if (tuple != null) {
                    for (Map.Entry<String, String> e : tuple.entrySet()) {
                        propParts.add(condVarName + "." + dim.prefix + e.getKey() + "_" + e.getValue() + "=" + dim.activeValue);
                    }
                } else {
                    for (String mode : condSmv.getModes()) {
                        List<String> ms = condSmv.getModeStates() != null ? condSmv.getModeStates().get(mode) : null;
                        if (ms != null && ms.contains(val)) {
                            propParts.add(condVarName + "." + dim.prefix + mode + "_" + val + "=" + dim.activeValue);
                            break;
                        }
                    }
                }
            }
        } else {
            for (String val : includeValues) {
                propParts.add(condVarName + "." + dim.prefix + val + "=" + dim.activeValue);
            }
        }
        if (propParts.isEmpty()) return null;
        return propParts.size() == 1 ? propParts.get(0) : "(" + String.join(" & ", propParts) + ")";
    }

    /**
     * Collect property condition parts for all states EXCEPT those in the given set.
     * Used for "!=" and "NOT IN" relations: ensure all other possible states are trusted/private.
     * When targetMode is non-null, only considers states within that specific mode.
     * When targetMode is null, processes all modes and handles tuple values via resolveStateTupleCandidate.
     */
    private String collectStatePropertyPartsExcluding(DeviceSmvData condSmv, String condVarName,
                                                      PropertyDimension dim, Set<String> excludeValues,
                                                      String targetMode) {
        List<String> propParts = new ArrayList<>();
        if (condSmv.getModes() != null && !condSmv.getModes().isEmpty()) {
            if (targetMode != null) {
                // Scoped to a single mode: exclude directly within that mode's states.
                List<String> modeStates = condSmv.getModeStates() != null ? condSmv.getModeStates().get(targetMode) : null;
                if (modeStates != null) {
                    for (String s : modeStates) {
                        if (!excludeValues.contains(s)) {
                            propParts.add(condVarName + "." + dim.prefix + targetMode + "_" + s + "=" + dim.activeValue);
                        }
                    }
                }
            } else {
                List<String> modes = condSmv.getModes();
                // Build per-mode exclusion sets from potentially tuple values.
                Map<String, Set<String>> perModeExclusions = new LinkedHashMap<>();
                for (String mode : modes) perModeExclusions.put(mode, new LinkedHashSet<>());

                for (String val : excludeValues) {
                    Map<String, String> tuple = resolveStateTupleCandidate(condSmv, val);
                    if (tuple != null) {
                        for (Map.Entry<String, String> e : tuple.entrySet()) {
                            perModeExclusions.get(e.getKey()).add(e.getValue());
                        }
                    } else {
                        for (String mode : modes) {
                            List<String> modeStates = condSmv.getModeStates() != null ? condSmv.getModeStates().get(mode) : null;
                            if (modeStates != null && modeStates.contains(val)) {
                                perModeExclusions.get(mode).add(val);
                            }
                        }
                    }
                }

                for (String mode : modes) {
                    List<String> modeStates = condSmv.getModeStates() != null ? condSmv.getModeStates().get(mode) : null;
                    if (modeStates != null) {
                        Set<String> excluded = perModeExclusions.get(mode);
                        for (String s : modeStates) {
                            if (!excluded.contains(s)) {
                                propParts.add(condVarName + "." + dim.prefix + mode + "_" + s + "=" + dim.activeValue);
                            }
                        }
                    }
                }
            }
        } else if (condSmv.getStates() != null) {
            for (String s : condSmv.getStates()) {
                if (!excludeValues.contains(s)) {
                    propParts.add(condVarName + "." + dim.prefix + s + "=" + dim.activeValue);
                }
            }
        }
        if (propParts.isEmpty()) return null;
        return propParts.size() == 1 ? propParts.get(0) : "(" + String.join(" & ", propParts) + ")";
    }

    /**
     * Build content privacy condition from rule command referencing contentDevice.content.
     * e.g. "THEN Facebook.post(MobilePhone.photo)" checks "mobilephone.privacy_photo=private"
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

        // Verify the content exists in the content device
        for (DeviceSmvData.ContentInfo ci : contentSmv.getContents()) {
            if (contentName.equals(ci.getName())) {
                return contentSmv.getVarName() + ".privacy_" + contentName + "=private";
            }
        }
        return null;
    }

    /**
     * Generate next() transitions for IsChangeable=true content privacy variables.
     * When a rule references this content (e.g. THEN Facebook.post(MobilePhone.photo)),
     * the content privacy is set to private; otherwise it keeps its current value.
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
     * Find rules whose command.contentDevice matches the given device and command.content matches the given content name.
     */
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

            List<DeviceManifest.InternalVariable> internalVars =
                    smv.getManifest().getInternalVariables() != null
                            ? smv.getManifest().getInternalVariables() : Collections.emptyList();

            for (String varName2 : smv.getImpactedVariables()) {
                boolean isEnum = false;
                for (DeviceManifest.InternalVariable var : internalVars) {
                    if (var.getName().equals(varName2) && var.getValues() != null && !var.getValues().isEmpty()) {
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
                                    if (firstCond) continue; // all segments empty — skip this CASE branch
                                    String rawRate = dynamic.getChangeRate();
                                    int parsedRate;
                                    try {
                                        parsedRate = Integer.parseInt(rawRate != null ? rawRate.trim() : "");
                                    } catch (NumberFormatException e) {
                                        log.warn("Device '{}': Dynamics.ChangeRate '{}' is not a valid integer, skipping",
                                                varName, rawRate);
                                        continue;
                                    }
                                    content.append(": ").append(parsedRate).append(";\n");
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
                if (lowerBound != null && upperBound != null && isAttack && isSensor) {
                    upperBound = SmvBoundsUtils.resolveEffectiveUpperBound(lowerBound, upperBound, true, intensity);
                }
                boolean hasNumericBounds = lowerBound != null && upperBound != null;

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

    private String clampExpr(String expr, Integer lower, Integer upper) {
        if (lower == null || upper == null) {
            return expr;
        }
        return clampExpr(expr, lower.intValue(), upper.intValue());
    }

    /**
     * Parse NaturalChangeRate string into [lowerRate, upperRate].
     * Supports formats: "3", "[-1,2]", etc.
     * Returns int[2] where [0]=lowerRate, [1]=upperRate.
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
     * Validate and clamp user-provided init value for an env variable.
     * Enum variables: value must be in the enum set; numeric variables: clamp to bounds.
     * Returns null if the value is invalid and should be skipped.
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
        // Fallback for variables without enum/range: assume default range 0..100 in main module
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
     * Normalize trigger relation and throw if unsupported for NuSMV.
     */
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
     * Handle IN/NOT_IN by expanding to SMV expressions: (x=a | x=b) or (x!=a & x!=b).
     * For other relations, returns left + relation + value directly.
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
     * Split value by ,;| delimiters for IN/NOT_IN; for other relations return the value as single-element list.
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
     * Clean state value via cleanStateName; for IN/NOT_IN, clean each segment individually.
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
