package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.component.nusmv.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

@Slf4j
@Component
public class SmvMainModuleBuilder {

    public String build(Long userId,
                       List<DeviceNodeDto> devices,
                       List<RuleDto> rules,
                       Map<String, DeviceSmvData> deviceSmvMap,
                       boolean isAttack,
                       int intensity) {

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
        
        if (isAttack && intensity > 0) {
            content.append("\nFROZENVAR");
            content.append("\n\tintensity: 0..50;");
        }
        
        content.append("\nVAR\n");

        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getId());
            if (smv == null) continue;

            String moduleName = smv.getModuleName();
            String varName = smv.getVarName();
            content.append("\t").append(varName).append(": ").append(moduleName).append(";\n");
        }

        Set<String> declaredEnvVars = new HashSet<>();
        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getId());
            if (smv == null || smv.envVariables == null) continue;

            for (String varName : smv.envVariables.keySet()) {
                if (!declaredEnvVars.contains(varName)) {
                    declaredEnvVars.add(varName);
                    DeviceManifest.InternalVariable var = smv.envVariables.get(varName);
                    content.append("\ta_").append(varName).append(": ");
                    if (var.getValues() != null && !var.getValues().isEmpty()) {
                        content.append("{").append(String.join(", ", var.getValues())).append("};\n");
                    } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                        content.append(var.getLowerBound()).append("..").append(var.getUpperBound()).append(";\n");
                    } else {
                        content.append("integer;\n");
                    }
                }
            }
        }

        content.append("\nASSIGN");

        if (isAttack && intensity > 0) {
            content.append("\n\tinit(intensity) := 0");
            for (DeviceNodeDto device : devices) {
                DeviceSmvData smv = deviceSmvMap.get(device.getId());
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
        appendTrustTransitions(content, devices, rules, deviceSmvMap, isAttack);
        appendPrivacyTransitions(content, devices, rules, deviceSmvMap, isAttack);
        appendVariableRateTransitions(content, devices, deviceSmvMap);
        appendSensorEnvAssignments(content, devices, deviceSmvMap);
        appendInternalVariableTransitions(content, devices, deviceSmvMap, isAttack);

        return content.toString();
    }

    private void appendSensorEnvAssignments(StringBuilder content,
                                           List<DeviceNodeDto> devices,
                                           Map<String, DeviceSmvData> deviceSmvMap) {
        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getId());
            if (smv == null || smv.manifest == null) continue;

            boolean isSensor = smv.manifest.getApis() == null || smv.manifest.getApis().isEmpty();
            if (!isSensor) continue;

            String varName = smv.getVarName();

            if (smv.manifest.getInternalVariables() != null) {
                for (DeviceManifest.InternalVariable var : smv.manifest.getInternalVariables()) {
                    if (var.getIsInside() != null && !var.getIsInside()) {
                        content.append("\n\t").append(varName).append(".").append(var.getName())
                               .append(" := a_").append(var.getName()).append(";\n");
                    }
                }
            }
        }
    }

    private void appendStateTransitions(StringBuilder content,
                                       List<DeviceNodeDto> devices,
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

        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getId());
            if (smv == null || smv.modes == null) continue;

            String varName = smv.getVarName();
            List<RuleDto> deviceRules = rulesByTarget.get(device.getId());

            if (smv.modes.size() > 1) {
                for (int modeIdx = 0; modeIdx < smv.modes.size(); modeIdx++) {
                    String mode = smv.modes.get(modeIdx);
                    List<String> modeStates = smv.modeStates.get(mode);
                    if (modeStates == null || modeStates.isEmpty()) continue;

                    content.append("\n\tnext(").append(varName).append(".").append(mode).append(") :=\n");
                    content.append("\tcase\n");

                     if (deviceRules != null) {
                        for (RuleDto rule : deviceRules) {
                                    if (rule.getCommand() == null || rule.getCommand().getAction() == null) {
                                        continue;
                                    }
                            if (rule.getCommand() == null || rule.getCommand().getAction() == null) {
                                continue;
                            }
                            String action = rule.getCommand().getAction();
                            
                            DeviceManifest.API matchedApi = findApi(smv.manifest, action);
                            if (matchedApi == null) continue;

                            String endState = getEndStateForMode(matchedApi.getEndState(), modeIdx);
                            if (endState == null || endState.isEmpty()) continue;

                            String startState = getEndStateForMode(matchedApi.getStartState(), modeIdx);
                            
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

                    if (smv.manifest != null && smv.manifest.getTransitions() != null) {
                        for (DeviceManifest.Transition trans : smv.manifest.getTransitions()) {
                            if (trans.getEndState() == null) continue;
                            String endState = getEndStateForMode(trans.getEndState(), modeIdx);
                            if (endState == null || endState.isEmpty()) continue;
                            
                            DeviceManifest.Trigger trigger = trans.getTrigger();
                            if (trigger != null) {
                                content.append("\t\t").append(varName).append(".")
                                       .append(trigger.getAttribute()).append(" ")
                                       .append(trigger.getRelation()).append(" ")
                                       .append(trigger.getValue()).append(": ").append(endState).append(";\n");
                            }
                        }
                    }

                    content.append("\t\tTRUE: ").append(varName).append(".").append(mode).append(";\n");
                    content.append("\tesac;\n");
                }
            } else {
                if (smv.states == null || smv.states.isEmpty()) continue;

                content.append("\n\tnext(").append(varName).append(".state) :=\n");
                content.append("\tcase\n");

                boolean isSensor = smv.manifest != null && 
                                  (smv.manifest.getApis() == null || smv.manifest.getApis().isEmpty());

                    if (deviceRules != null) {
                        for (RuleDto rule : deviceRules) {
                                    if (rule.getCommand() == null || rule.getCommand().getAction() == null) {
                                        continue;
                                    }
                            if (rule.getCommand() == null || rule.getCommand().getAction() == null) {
                                continue;
                            }
                            String action = rule.getCommand().getAction();
                        
                        DeviceManifest.API matchedApi = findApi(smv.manifest, action);
                        if (matchedApi == null) continue;

                        String endState = matchedApi.getEndState();
                        if (endState == null || endState.isEmpty()) continue;

                        String startState = matchedApi.getStartState();
                        
                        content.append("\t\t");
                        appendRuleConditions(content, rule, deviceSmvMap);
                        
                        if (startState != null && !startState.isEmpty()) {
                            content.append(" & ").append(varName).append(".state=").append(startState);
                        }
                        
                        if (isAttack && isSensor) {
                            content.append(" & ").append(varName).append(".is_attack=FALSE");
                        }
                        
                        content.append(": ").append(endState).append(";\n");
                    }
                }

                if (smv.transitions != null) {
                    for (DeviceSmvData.TransitionInfo trans : smv.transitions) {
                        if (trans.condition != null && !trans.condition.isEmpty() && trans.nextState != null) {
                            content.append("\t\t").append(trans.condition).append(": ").append(trans.nextState).append(";\n");
                        }
                    }
                }

                for (String state : smv.states) {
                    content.append("\t\t").append(varName).append(".state=").append(state);
                    if (isSensor && isAttack) {
                        content.append(" | ").append(varName).append(".is_attack=TRUE");
                    }
                    content.append(": ").append(state).append(";\n");
                }

                content.append("\t\tTRUE: ").append(varName).append(".state;\n");
                content.append("\tesac;\n");
            }
        }
    }

    private void appendRuleConditions(StringBuilder content, RuleDto rule, Map<String, DeviceSmvData> deviceSmvMap) {
        if (rule.getConditions() == null || rule.getConditions().isEmpty()) {
            content.append("TRUE");
            return;
        }

        boolean first = true;
        for (RuleDto.Condition condition : rule.getConditions()) {
            if (condition == null) continue;
            
            if (!first) {
                content.append(" & ");
            }
            first = false;

            String deviceId = condition.getDeviceName();
            DeviceSmvData condSmv = deviceSmvMap.get(deviceId);
            
            if (condSmv == null) {
                // Device not found, use raw device name as fallback
                if (condition.getRelation() != null) {
                    content.append(deviceId).append(".").append(condition.getAttribute())
                           .append(condition.getRelation()).append(condition.getValue());
                } else {
                    content.append(deviceId).append(".").append(condition.getAttribute());
                }
            } else {
                String varName = condSmv.getVarName();
                
                if (condition.getRelation() != null) {
                    // Normal variable/state condition: device.attribute relation value
                    content.append(varName).append(".").append(condition.getAttribute())
                           .append(condition.getRelation()).append(condition.getValue());
                } else {
                    // API signal condition: use api signal OR state-based condition
                    DeviceManifest manifest = condSmv.manifest;
                    if (manifest != null && manifest.getApis() != null) {
                        for (DeviceManifest.API api : manifest.getApis()) {
                            if (api.getSignal() != null && api.getSignal() && 
                                api.getName().equals(condition.getAttribute())) {
                                String endState = api.getEndState();
                                if (endState != null) {
                                    String apiSignal = buildApiSignalName(api.getName());
                                    String apiSignalExpr = apiSignal != null
                                            ? varName + "." + apiSignal + "=TRUE"
                                            : null;
                                    // Handle multi-mode devices
                                    if (condSmv.modes != null && !condSmv.modes.isEmpty()) {
                                        int modeIdx = getModeIndexOfState(condSmv, endState);
                                        if (modeIdx >= 0 && modeIdx < condSmv.modes.size()) {
                                            String mode = condSmv.modes.get(modeIdx);
                                            String cleanEndState = endState.replace(";", "").replace(" ", "");
                                            String stateExpr = varName + "." + mode + "=" + cleanEndState;
                                            if (apiSignalExpr != null) {
                                                content.append("(").append(apiSignalExpr).append(" | ").append(stateExpr).append(")");
                                            } else {
                                                content.append(stateExpr);
                                            }
                                        }
                                    } else {
                                        // Single mode device
                                        String cleanEndState = endState.replace(";", "").replace(" ", "");
                                        String stateExpr = varName + ".state=" + cleanEndState;
                                        if (apiSignalExpr != null) {
                                            content.append("(").append(apiSignalExpr).append(" | ").append(stateExpr).append(")");
                                        } else {
                                            content.append(stateExpr);
                                        }
                                    }
                                }
                                break;
                            }
                        }
                    }
                }
            }
        }
        
        if (first) {
            content.append("TRUE");
        }
    }

    private void appendRuleTrustConditions(StringBuilder content, RuleDto rule, Map<String, DeviceSmvData> deviceSmvMap) {
        if (rule.getConditions() == null || rule.getConditions().isEmpty()) {
            content.append("TRUE");
            return;
        }

        boolean first = true;
        for (RuleDto.Condition condition : rule.getConditions()) {
            if (condition == null || condition.getDeviceName() == null) continue;

            DeviceSmvData condSmv = deviceSmvMap.get(condition.getDeviceName());
            if (condSmv == null) continue;

            if (!first) {
                content.append(" | ");
            }
            first = false;

            String condVarName = condSmv.getVarName();
            DeviceManifest deviceManifest = condSmv.manifest;

            if (deviceManifest == null) continue;

            if (condition.getRelation() == null) {
                if (deviceManifest.getApis() != null) {
                    for (DeviceManifest.API api : deviceManifest.getApis()) {
                        if (api.getName().equals(condition.getAttribute()) && api.getSignal()) {
                            String endState = api.getEndState();
                            if (endState != null) {
                                if (condSmv.modes != null && !condSmv.modes.isEmpty()) {
                                    int modeIdx = getModeIndexOfState(condSmv, endState);
                                    if (modeIdx >= 0 && modeIdx < condSmv.modes.size()) {
                                        String mode = condSmv.modes.get(modeIdx);
                                        String cleanEndState = endState.replace(";", "").replace(" ", "");
                                        content.append(condVarName).append(".trust_").append(mode)
                                               .append("_").append(cleanEndState).append("=trusted");
                                    }
                                } else {
                                    String cleanEndState = endState.replace(";", "").replace(" ", "");
                                    content.append(condVarName).append(".trust_").append(cleanEndState).append("=trusted");
                                }
                            }
                            break;
                        }
                    }
                }
            } else {
                boolean isVariable = false;
                if (deviceManifest.getInternalVariables() != null) {
                    for (DeviceManifest.InternalVariable var : deviceManifest.getInternalVariables()) {
                        if (var.getName().equals(condition.getAttribute())) {
                            content.append(condVarName).append(".trust_").append(var.getName()).append("=trusted");
                            isVariable = true;
                            break;
                        }
                    }
                }
                
                if (!isVariable && "=".equals(condition.getRelation())) {
                    String stateValue = condition.getValue().replace(" ", "");
                    if (condSmv.modes != null && !condSmv.modes.isEmpty()) {
                        for (String mode : condSmv.modes) {
                            List<String> modeStates = condSmv.modeStates.get(mode);
                            if (modeStates != null && modeStates.contains(condition.getAttribute())) {
                                content.append(condVarName).append(".trust_").append(mode)
                                       .append("_").append(stateValue).append("=trusted");
                                break;
                            }
                        }
                    } else {
                        content.append(condVarName).append(".trust_").append(stateValue).append("=trusted");
                    }
                }
            }
        }

        if (first) {
            content.append("TRUE");
        }
    }

    private void appendEnvTransitions(StringBuilder content,
                                     List<DeviceNodeDto> devices,
                                     Map<String, DeviceSmvData> deviceSmvMap) {
        
        Set<String> processedVars = new HashSet<>();

        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getId());
            if (smv == null || smv.envVariables == null) continue;

            for (String varName : smv.envVariables.keySet()) {
                if (processedVars.contains(varName)) continue;
                processedVars.add(varName);

                DeviceManifest.InternalVariable var = smv.envVariables.get(varName);
                String smvVarName = "a_" + varName;
                
                content.append("\n\tnext(").append(smvVarName).append(") :=\n");
                content.append("\tcase\n");

                for (DeviceNodeDto dev : devices) {
                    DeviceSmvData transSmv = deviceSmvMap.get(dev.getId());
                    if (transSmv == null || transSmv.manifest == null || 
                        transSmv.manifest.getTransitions() == null) continue;

                    for (DeviceManifest.Transition trans : transSmv.manifest.getTransitions()) {
                        if (trans.getAssignments() == null) continue;
                        
                        for (DeviceManifest.Assignment assignment : trans.getAssignments()) {
                            if (varName.equals(assignment.getAttribute())) {
                                DeviceManifest.Trigger trigger = trans.getTrigger();
                                if (trigger != null) {
                                    content.append("\t\t").append(transSmv.getVarName()).append(".")
                                           .append(trigger.getAttribute()).append(" ")
                                           .append(trigger.getRelation()).append(" ")
                                           .append(trigger.getValue()).append(": ").append(assignment.getValue()).append(";\n");
                                }
                            }
                        }
                    }
                }

                if (var.getValues() != null && !var.getValues().isEmpty()) {
                    content.append("\t\tTRUE: {").append(String.join(", ", var.getValues())).append("};\n");
                } else {
                    content.append("\t\tTRUE: ").append(smvVarName).append(";\n");
                }
                
                content.append("\tesac;\n");
            }
        }
    }

    private void appendApiSignalTransitions(StringBuilder content,
                                           List<DeviceNodeDto> devices,
                                           Map<String, DeviceSmvData> deviceSmvMap) {
        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getId());
            if (smv == null || smv.manifest == null || smv.manifest.getApis() == null) continue;

            String varName = smv.getVarName();

            for (DeviceManifest.API api : smv.manifest.getApis()) {
                if (api.getSignal() == null || !api.getSignal()) continue;

                String signalName = buildApiSignalName(api.getName());
                if (signalName == null) {
                    continue;
                }
                
                content.append("\n\tnext(").append(varName).append(".").append(signalName).append(") :=\n");
                content.append("\tcase\n");

                String endState = api.getEndState();
                String startState = api.getStartState();
                
                if (smv.modes != null && !smv.modes.isEmpty()) {
                    int modeIdx = getModeIndexOfState(smv, endState);
                    if (modeIdx >= 0 && modeIdx < smv.modes.size()) {
                        String mode = smv.modes.get(modeIdx);
                        String cleanEndState = endState.replace(";", "").replace(" ", "");
                        String cleanStartState = startState != null ? startState.replace(";", "").replace(" ", "") : "";
                        
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
                    if (startState == null || startState.isEmpty()) {
                        content.append("\t\t").append(varName).append(".state!=").append(endState)
                               .append(" & next(").append(varName).append(".state)=").append(endState).append(": TRUE;\n");
                    } else {
                        content.append("\t\t").append(varName).append(".state=").append(startState)
                               .append(" & next(").append(varName).append(".state)=").append(endState).append(": TRUE;\n");
                    }
                }

                content.append("\t\tTRUE: FALSE;\n");
                content.append("\tesac;\n");
            }
        }
    }

    private void appendTrustTransitions(StringBuilder content,
                                       List<DeviceNodeDto> devices,
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

        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getId());
            if (smv == null) continue;

            if (isSensorDevice(smv)) {
                continue;
            }

            String varName = smv.getVarName();
            List<RuleDto> deviceRules = rulesByTarget.get(device.getId());

            if (smv.modes != null && smv.modes.size() > 1) {
                for (int i = 0; i < smv.modes.size(); i++) {
                    String mode = smv.modes.get(i);
                    List<String> modeStates = smv.modeStates.get(mode);
                    if (modeStates == null) continue;

                    for (String state : modeStates) {
                        content.append("\n\tnext(").append(varName).append(".trust_")
                               .append(mode).append("_").append(state.replace(" ", "")).append(") :=\n");
                        content.append("\tcase\n");

                        if (isAttack) {
                            content.append("\t\t").append(varName).append(".is_attack=TRUE: untrusted;\n");
                        }

                        if (deviceRules != null) {
                            for (RuleDto rule : deviceRules) {
                                    if (rule.getCommand() == null || rule.getCommand().getAction() == null) {
                                        continue;
                                    }
                                String action = rule.getCommand().getAction();
                                DeviceManifest.API api = findApi(smv.manifest, action);
                                if (api == null) continue;

                                String endState = getEndStateForMode(api.getEndState(), i);
                                if (endState != null && endState.replace(" ", "").equals(state.replace(" ", ""))) {
                                    content.append("\t\t");
                                    appendRuleConditions(content, rule, deviceSmvMap);
                                    content.append(" & (");
                                    appendRuleTrustConditions(content, rule, deviceSmvMap);
                                    content.append("): trusted;\n");
                                    
                                    content.append("\t\t");
                                    appendRuleConditions(content, rule, deviceSmvMap);
                                    content.append(": untrusted;\n");
                                }
                            }
                        }

                        content.append("\t\tTRUE: ").append(varName).append(".trust_")
                               .append(mode).append("_").append(state.replace(" ", "")).append(";\n");
                        content.append("\tesac;\n");
                    }
                }
            } else if (smv.states != null) {
                for (String state : smv.states) {
                    content.append("\n\tnext(").append(varName).append(".trust_").append(state).append(") :=\n");
                    content.append("\tcase\n");

                    if (isAttack) {
                        content.append("\t\t").append(varName).append(".is_attack=TRUE: untrusted;\n");
                    }

                    if (deviceRules != null) {
                        for (RuleDto rule : deviceRules) {
                                    if (rule.getCommand() == null || rule.getCommand().getAction() == null) {
                                        continue;
                                    }
                            String action = rule.getCommand().getAction();
                            DeviceManifest.API api = findApi(smv.manifest, action);
                            if (api != null && state.equals(api.getEndState())) {
                                content.append("\t\t");
                                appendRuleConditions(content, rule, deviceSmvMap);
                                content.append(" & (");
                                appendRuleTrustConditions(content, rule, deviceSmvMap);
                                content.append("): trusted;\n");
                                
                                content.append("\t\t");
                                appendRuleConditions(content, rule, deviceSmvMap);
                                content.append(": untrusted;\n");
                            }
                        }
                    }

                    content.append("\t\tTRUE: ").append(varName).append(".trust_").append(state).append(";\n");
                    content.append("\tesac;\n");
                }
            }
        }
    }

    private void appendPrivacyTransitions(StringBuilder content,
                                          List<DeviceNodeDto> devices,
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

        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getId());
            if (smv == null) continue;

            if (isSensorDevice(smv)) {
                continue;
            }

            String varName = smv.getVarName();
            List<RuleDto> deviceRules = rulesByTarget.get(device.getId());

            if (smv.modes != null && smv.modes.size() > 1) {
                for (int i = 0; i < smv.modes.size(); i++) {
                    String mode = smv.modes.get(i);
                    List<String> modeStates = smv.modeStates.get(mode);
                    if (modeStates == null) continue;

                    for (String state : modeStates) {
                        content.append("\n\tnext(").append(varName).append(".privacy_")
                               .append(mode).append("_").append(state.replace(" ", "")).append(") :=\n");
                        content.append("\tcase\n");

                        if (deviceRules != null) {
                            for (RuleDto rule : deviceRules) {
                                    if (rule.getCommand() == null || rule.getCommand().getAction() == null) {
                                        continue;
                                    }
                                String action = rule.getCommand().getAction();
                                DeviceManifest.API api = findApi(smv.manifest, action);
                                if (api == null) continue;

                                String endState = getEndStateForMode(api.getEndState(), i);
                                if (endState != null && endState.replace(" ", "").equals(state.replace(" ", ""))) {
                                    content.append("\t\t");
                                    appendRuleConditions(content, rule, deviceSmvMap);
                                    content.append(" & (");
                                    appendRulePrivacyConditions(content, rule, deviceSmvMap);
                                    content.append("): private;\n");
                                }
                            }
                        }

                        content.append("\t\tTRUE: ").append(varName).append(".privacy_")
                               .append(mode).append("_").append(state.replace(" ", "")).append(";\n");
                        content.append("\tesac;\n");
                    }
                }
            } else if (smv.states != null) {
                for (String state : smv.states) {
                    content.append("\n\tnext(").append(varName).append(".privacy_").append(state).append(") :=\n");
                    content.append("\tcase\n");

                    if (deviceRules != null) {
                        for (RuleDto rule : deviceRules) {
                                    if (rule.getCommand() == null || rule.getCommand().getAction() == null) {
                                        continue;
                                    }
                            String action = rule.getCommand().getAction();
                            DeviceManifest.API api = findApi(smv.manifest, action);
                            if (api != null && state.equals(api.getEndState())) {
                                content.append("\t\t");
                                appendRuleConditions(content, rule, deviceSmvMap);
                                content.append(" & (");
                                appendRulePrivacyConditions(content, rule, deviceSmvMap);
                                content.append("): private;\n");
                            }
                        }
                    }

                    content.append("\t\tTRUE: ").append(varName).append(".privacy_").append(state).append(";\n");
                    content.append("\tesac;\n");
                }
            }
        }
    }

    private void appendRulePrivacyConditions(StringBuilder content, RuleDto rule, Map<String, DeviceSmvData> deviceSmvMap) {
        if (rule.getConditions() == null || rule.getConditions().isEmpty()) {
            content.append("TRUE");
            return;
        }

        boolean first = true;
        for (RuleDto.Condition condition : rule.getConditions()) {
            if (condition == null || condition.getDeviceName() == null) continue;

            DeviceSmvData condSmv = deviceSmvMap.get(condition.getDeviceName());
            if (condSmv == null) continue;

            if (!first) {
                content.append(" | ");
            }
            first = false;

            String condVarName = condSmv.getVarName();
            DeviceManifest deviceManifest = condSmv.manifest;

            if (deviceManifest == null) continue;

            if (condition.getRelation() == null) {
                if (deviceManifest.getApis() != null) {
                    for (DeviceManifest.API api : deviceManifest.getApis()) {
                        if (api.getName().equals(condition.getAttribute()) && api.getSignal()) {
                            String endState = api.getEndState();
                            if (endState != null) {
                                if (condSmv.modes != null && !condSmv.modes.isEmpty()) {
                                    int modeIdx = getModeIndexOfState(condSmv, endState);
                                    if (modeIdx >= 0 && modeIdx < condSmv.modes.size()) {
                                        String mode = condSmv.modes.get(modeIdx);
                                        String cleanEndState = endState.replace(";", "").replace(" ", "");
                                        content.append(condVarName).append(".privacy_").append(mode)
                                               .append("_").append(cleanEndState).append("=private");
                                    }
                                } else {
                                    String cleanEndState = endState.replace(";", "").replace(" ", "");
                                    content.append(condVarName).append(".privacy_").append(cleanEndState).append("=private");
                                }
                            }
                            break;
                        }
                    }
                }
            } else {
                boolean isVariable = false;
                if (deviceManifest.getInternalVariables() != null) {
                    for (DeviceManifest.InternalVariable var : deviceManifest.getInternalVariables()) {
                        if (var.getName().equals(condition.getAttribute())) {
                            content.append(condVarName).append(".privacy_").append(var.getName()).append("=private");
                            isVariable = true;
                            break;
                        }
                    }
                }
                
                if (!isVariable && "=".equals(condition.getRelation())) {
                    String stateValue = condition.getValue().replace(" ", "");
                    if (condSmv.modes != null && !condSmv.modes.isEmpty()) {
                        for (String mode : condSmv.modes) {
                            List<String> modeStates = condSmv.modeStates.get(mode);
                            if (modeStates != null && modeStates.contains(condition.getAttribute())) {
                                content.append(condVarName).append(".privacy_").append(mode)
                                       .append("_").append(stateValue).append("=private");
                                break;
                            }
                        }
                    } else {
                        content.append(condVarName).append(".privacy_").append(stateValue).append("=private");
                    }
                }
            }
        }

        if (first) {
            content.append("TRUE");
        }
    }

    private void appendVariableRateTransitions(StringBuilder content,
                                              List<DeviceNodeDto> devices,
                                              Map<String, DeviceSmvData> deviceSmvMap) {
        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getId());
            if (smv == null || smv.impactedVariables == null || smv.manifest == null) continue;

            String varName = smv.getVarName();

            for (String varName2 : smv.impactedVariables) {
                boolean isEnum = false;
                for (DeviceManifest.InternalVariable var : smv.variables) {
                    if (var.getName().equals(varName2) && var.getValues() != null) {
                        isEnum = true;
                        break;
                    }
                }
                if (isEnum) continue;

                content.append("\n\tnext(").append(varName).append(".").append(varName2).append("_rate) :=\n");
                content.append("\tcase\n");

                if (smv.manifest.getWorkingStates() != null) {
                    for (DeviceManifest.WorkingState state : smv.manifest.getWorkingStates()) {
                        if (state.getDynamics() == null) continue;
                        
                        for (DeviceManifest.Dynamic dynamic : state.getDynamics()) {
                            if (varName2.equals(dynamic.getVariableName())) {
                                if (smv.modes != null && smv.modes.size() > 1) {
                                    String[] states = state.getName().split(";");
                                    content.append("\t\t");
                                    for (int c = 0; c < smv.modes.size(); c++) {
                                        if (c > 0) content.append(" & ");
                                        content.append(varName).append(".").append(smv.modes.get(c))
                                               .append("=").append(states[c].replace(" ", ""));
                                    }
                                    content.append(": ").append(dynamic.getChangeRate()).append(";\n");
                                } else {
                                    content.append("\t\t").append(varName).append(".state=")
                                           .append(state.getName()).append(": ").append(dynamic.getChangeRate()).append(";\n");
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
                                                  List<DeviceNodeDto> devices,
                                                  Map<String, DeviceSmvData> deviceSmvMap,
                                                  boolean isAttack) {
        for (DeviceNodeDto device : devices) {
            DeviceSmvData smv = deviceSmvMap.get(device.getId());
            if (smv == null || smv.manifest == null || smv.manifest.getInternalVariables() == null) continue;

            String varName = smv.getVarName();
            boolean isSensor = smv.manifest.getApis() == null || smv.manifest.getApis().isEmpty();

            for (DeviceManifest.InternalVariable var : smv.manifest.getInternalVariables()) {
                if (var.getIsInside() == null || !var.getIsInside()) {
                    continue;
                }

                content.append("\n\tnext(").append(varName).append(".").append(var.getName()).append(") :=\n");
                content.append("\tcase\n");

                if (isAttack && isSensor) {
                    content.append("\t\t").append(varName).append(".is_attack=TRUE: ");
                    if (var.getValues() != null && !var.getValues().isEmpty()) {
                        content.append("{").append(String.join(", ", var.getValues())).append("};\n");
                    } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                        content.append(var.getLowerBound()).append("..").append(var.getUpperBound()).append(";\n");
                    } else {
                        content.append("0..100;\n");
                    }
                }

                if (smv.manifest.getTransitions() != null) {
                    for (DeviceManifest.Transition trans : smv.manifest.getTransitions()) {
                        if (trans.getAssignments() == null) continue;
                        
                        for (DeviceManifest.Assignment assignment : trans.getAssignments()) {
                            if (var.getName().equals(assignment.getAttribute())) {
                                DeviceManifest.Trigger trigger = trans.getTrigger();
                                if (trigger != null) {
                                    content.append("\t\t").append(varName).append(".")
                                           .append(trigger.getAttribute()).append(" ")
                                           .append(trigger.getRelation()).append(" ")
                                           .append(trigger.getValue()).append(": ").append(assignment.getValue()).append(";\n");
                                }
                            }
                        }
                    }
                }

                if (var.getValues() == null || var.getValues().isEmpty()) {
                    String impactedRate = "";
                    if (smv.impactedVariables != null && smv.impactedVariables.contains(var.getName())) {
                        impactedRate = varName + "." + var.getName() + "_rate";
                    }

                    String[] changeRate = var.getNaturalChangeRate() != null ? 
                        var.getNaturalChangeRate().split("\\[|]|, ") : new String[]{"0"};
                    
                    if (changeRate.length == 1) {
                        int rate = Integer.parseInt(changeRate[0]);
                        if (rate > 0) {
                            content.append("\t\t").append(varName).append(".").append(var.getName())
                                   .append(">=").append(var.getUpperBound()).append(": ").append(var.getUpperBound()).append(";\n");
                        } else if (rate < 0) {
                            content.append("\t\t").append(varName).append(".").append(var.getName())
                                   .append("<=").append(var.getLowerBound()).append(": ").append(var.getLowerBound()).append(";\n");
                        }
                        
                        if (!impactedRate.isEmpty()) {
                            content.append("\t\tTRUE: ").append(varName).append(".").append(var.getName())
                                   .append("+").append(rate).append("+").append(impactedRate).append(";\n");
                        } else {
                            content.append("\t\tTRUE: ").append(varName).append(".").append(var.getName())
                                   .append("+").append(rate).append(";\n");
                        }
                    } else {
                        int lowerRate = Integer.parseInt(changeRate[1]);
                        int upperRate = Integer.parseInt(changeRate[2]);
                        
                        content.append("\t\tTRUE: {");
                        if (lowerRate < 0) {
                            content.append(varName).append(".").append(var.getName()).append("+").append(lowerRate).append(", ");
                        }
                        content.append(varName).append(".").append(var.getName());
                        if (upperRate > 0) {
                            content.append(", ").append(varName).append(".").append(var.getName()).append("+").append(upperRate);
                        }
                        content.append("};\n");
                    }
                } else {
                    content.append("\t\tTRUE: {").append(String.join(", ", var.getValues())).append("};\n");
                }

                content.append("\tesac;\n");
            }
        }
    }

    private DeviceManifest.API findApi(DeviceManifest manifest, String actionName) {
        if (manifest == null || manifest.getApis() == null || actionName == null) return null;
        for (DeviceManifest.API api : manifest.getApis()) {
            if (actionName.equals(api.getName())) {
                return api;
            }
        }
        return null;
    }

    private String getEndStateForMode(String endState, int modeIndex) {
        if (endState == null) return null;
        String[] states = endState.split(";");
        if (modeIndex < states.length) {
            return states[modeIndex].trim();
        }
        return null;
    }

    private int getModeIndexOfState(DeviceSmvData smv, String state) {
        if (smv == null || smv.modes == null || state == null) return -1;
        
        for (int i = 0; i < smv.modes.size(); i++) {
            if (state.contains(smv.modes.get(i))) {
                return i;
            }
        }
        return 0;
    }

    private boolean isSensorDevice(DeviceSmvData smv) {
        return smv != null && smv.manifest != null &&
                (smv.manifest.getApis() == null || smv.manifest.getApis().isEmpty());
    }

    private String buildApiSignalName(String raw) {
        if (raw == null) return null;
        String cleaned = raw.replaceAll("[^a-zA-Z0-9_]", "_");
        if (cleaned.isBlank()) {
            return null;
        }
        return cleaned + "_a";
    }
}
