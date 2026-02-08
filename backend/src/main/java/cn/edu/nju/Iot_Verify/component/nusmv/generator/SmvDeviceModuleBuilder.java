package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

/**
 * SMV 设备模块构建器
 * 职责：构建单个设备的 NuSMV 模块定义
 */
@Slf4j
@Component
public class SmvDeviceModuleBuilder {

    private static final String NUSMV_FALSE = "FALSE";
    private static final String TRUST_TYPE = "{trusted, untrusted}";
    private static final String DEFAULT_PRIVACY = "public";
    private static final String DEFAULT_TRUST = "trusted";
    private static final String API_SIGNAL_TYPE = "api";

    public String build(DeviceSmvData smv, boolean isAttack) {
        // 参数验证
        if (smv == null) {
            log.error("SmvDeviceModuleBuilder.build: smv 参数不能为 null");
            throw new IllegalArgumentException("smv 参数不能为 null");
        }
        if (smv.getModuleName() == null || smv.getModuleName().isEmpty()) {
            log.error("SmvDeviceModuleBuilder.build: smv.getModuleName() 返回空字符串");
            throw new IllegalArgumentException("设备模块名称不能为空");
        }

        StringBuilder content = new StringBuilder();
        String moduleName = smv.getModuleName();

        content.append("\nMODULE ").append(moduleName);

        // 检查 manifest 是否为 null
        if (smv.manifest == null) {
            log.warn("SmvDeviceModuleBuilder.build: smv.manifest 为 null，将视为传感器设备");
            smv.manifest = new DeviceManifest();
        }

        boolean isSensor = smv.manifest.getApis() == null || smv.manifest.getApis().isEmpty();

        // FROZENVAR for sensors (attack mode + variable trust/privacy)
        appendFrozenVarSection(content, smv, isAttack, isSensor);

        appendVariables(content, smv, isSensor);
        appendAssignments(content, smv, isAttack, isSensor);

        return content.toString();
    }

    private void appendFrozenVarSection(StringBuilder content, DeviceSmvData smv, boolean isAttack, boolean isSensor) {
        boolean hasFrozenVar = false;
        StringBuilder frozenVars = new StringBuilder();

        if (isAttack) {
            frozenVars.append("\n\tis_attack: boolean;");
            hasFrozenVar = true;
        }

        if (isSensor) {
            for (DeviceManifest.InternalVariable var : smv.variables) {
                frozenVars.append("\n\ttrust_").append(var.getName()).append(": {trusted, untrusted};");
                frozenVars.append("\n\tprivacy_").append(var.getName()).append(": {public, private};");
                hasFrozenVar = true;
            }
        }

        if (hasFrozenVar) {
            content.append("\nFROZENVAR").append(frozenVars);
        }
    }

    private void appendVariables(StringBuilder content, DeviceSmvData smv, boolean isSensor) {
        content.append("\nVAR\n");

        appendModeVariables(content, smv);
        appendInternalVariables(content, smv);
        appendSignalVariables(content, smv);
        appendVariableRates(content, smv);
        appendTrustVariables(content, smv, isSensor);
        appendPrivacyVariables(content, smv, isSensor);
    }

    private void appendAssignments(StringBuilder content, DeviceSmvData smv, boolean isAttack, boolean isSensor) {
        content.append("\nASSIGN\n");

        appendInitialValues(content, smv, isSensor);

        if (isAttack) {
            content.append("\n\tinit(is_attack) := {TRUE, FALSE};");
        }

        appendInitialPrivacy(content, smv, isSensor);
        appendInitialTrust(content, smv, isAttack, isSensor);
        appendTransitions(content, smv, isAttack, isSensor);
    }

    private void appendModeVariables(StringBuilder content, DeviceSmvData smv) {
        if (smv.modes.size() <= 1) {
            if (!smv.states.isEmpty()) {
                content.append("\tstate: {").append(String.join(", ", smv.states)).append("};");
            }
        } else {
            for (String mode : smv.modes) {
                List<String> modeStateList = smv.modeStates.get(mode);
                if (modeStateList != null && !modeStateList.isEmpty()) {
                    content.append("\t").append(mode).append(": {").append(String.join(", ", modeStateList)).append("};");
                }
            }
        }
    }

    private void appendInternalVariables(StringBuilder content, DeviceSmvData smv) {
        for (DeviceManifest.InternalVariable var : smv.variables) {
            String varDef;
            if (var.getValues() != null && !var.getValues().isEmpty()) {
                varDef = "{" + String.join(", ", var.getValues()) + "}";
            } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                varDef = var.getLowerBound() + ".." + var.getUpperBound();
            } else {
                varDef = "boolean";
            }
            content.append("\n\t").append(var.getName()).append(": ").append(varDef).append(";");
        }
    }

    private void appendSignalVariables(StringBuilder content, DeviceSmvData smv) {
        for (DeviceSmvData.SignalInfo sig : smv.signalVars) {
            content.append("\n\t").append(sig.getName()).append(": boolean;");
        }
    }

    private void appendVariableRates(StringBuilder content, DeviceSmvData smv) {
        for (String varName : smv.impactedVariables) {
            content.append("\n\t").append(varName).append("_rate: integer;");
        }
    }

    private void appendTrustVariables(StringBuilder content, DeviceSmvData smv, boolean isSensor) {
        if (isSensor) {
            return;
        }

        List<String> modes = smv.modes;
        if (modes.size() <= 1) {
            for (String state : smv.states) {
                content.append("\n\ttrust_").append(state).append(": ").append(TRUST_TYPE).append(";");
            }
        } else {
            for (String mode : modes) {
                List<String> states = smv.modeStates.get(mode);
                if (states != null) {
                    for (String state : states) {
                        content.append("\n\ttrust_").append(mode).append("_").append(state).append(": ").append(TRUST_TYPE).append(";");
                    }
                }
            }
        }

        for (DeviceManifest.InternalVariable var : smv.variables) {
            content.append("\n\ttrust_").append(var.getName()).append(": ").append(TRUST_TYPE).append(";");
        }
    }

    private void appendPrivacyVariables(StringBuilder content, DeviceSmvData smv, boolean isSensor) {
        if (isSensor) {
            return;
        }

        List<String> modes = smv.modes;
        if (modes.size() <= 1) {
            for (String state : smv.states) {
                content.append("\n\tprivacy_").append(state).append(": {public, private};");
            }
        } else {
            for (String mode : modes) {
                List<String> states = smv.modeStates.get(mode);
                if (states != null) {
                    for (String state : states) {
                        content.append("\n\tprivacy_").append(mode).append("_").append(state).append(": {public, private};");
                    }
                }
            }
        }

        for (DeviceManifest.InternalVariable var : smv.variables) {
            content.append("\n\tprivacy_").append(var.getName()).append(": {public, private};");
        }
    }

    private void appendInitialValues(StringBuilder content, DeviceSmvData smv, boolean isSensor) {
        if (smv.modes.size() > 1) {
            for (String mode : smv.modes) {
                String initModeState = smv.currentModeStates.getOrDefault(mode, 
                    smv.modeStates.getOrDefault(mode, java.util.Collections.singletonList("")).get(0));
                if (!initModeState.isEmpty()) {
                    content.append("\n\tinit(").append(mode).append(") := ").append(initModeState).append(";");
                }
            }
        } else {
            String initState = smv.currentState != null ? smv.currentState :
                              (smv.states.isEmpty() ? "" : smv.states.get(0));
            if (!initState.isEmpty()) {
                content.append("\n\tinit(state) := ").append(initState).append(";");
            }
        }

        for (DeviceManifest.InternalVariable var : smv.variables) {
            if (var.getValues() != null && !var.getValues().isEmpty()) {
                String initValue = smv.variableValues.getOrDefault(var.getName(), var.getValues().get(0));
                content.append("\n\tinit(").append(var.getName()).append(") := ").append(initValue).append(";");
            } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                String initValue = smv.variableValues.getOrDefault(var.getName(), String.valueOf(var.getLowerBound()));
                content.append("\n\tinit(").append(var.getName()).append(") := ").append(initValue).append(";");
            }
        }

        for (DeviceSmvData.SignalInfo sig : smv.signalVars) {
            content.append("\n\tinit(").append(sig.getName()).append(") := ").append(NUSMV_FALSE).append(";");
        }

        for (String varName : smv.impactedVariables) {
            content.append("\n\tinit(").append(varName).append("_rate) := 0;");
        }
    }

    private void appendInitialTrust(StringBuilder content, DeviceSmvData smv, boolean isAttack, boolean isSensor) {
        String instanceTrust = smv.instanceStateTrust;
        List<String> modes = smv.modes;
        if (modes.size() > 1) {
            Set<String> initializedStates = new HashSet<>();
            if (smv.manifest != null && smv.manifest.getWorkingStates() != null) {
                for (DeviceManifest.WorkingState state : smv.manifest.getWorkingStates()) {
                    String[] mStates = state.getName().split(";");
                    for (int i = 0; i < modes.size() && i < mStates.length; i++) {
                        String stateKey = modes.get(i) + "_" + mStates[i].replace(" ", "");
                        if (initializedStates.contains(stateKey)) {
                            continue;
                        }
                        initializedStates.add(stateKey);
                        String trust = instanceTrust != null ? instanceTrust :
                                (state.getTrust() != null ? state.getTrust() : DEFAULT_TRUST);
                        content.append("\n\tinit(trust_").append(modes.get(i)).append("_").append(mStates[i].replace(" ", ""))
                               .append(") := ").append(trust).append(";");
                    }
                }
            }
            for (String mode : modes) {
                List<String> states = smv.modeStates.get(mode);
                if (states == null) continue;
                for (String state : states) {
                    String key = mode + "_" + state;
                    if (initializedStates.contains(key)) continue;
                    initializedStates.add(key);
                    String trust = instanceTrust != null ? instanceTrust :
                            smv.modeStateTrust.getOrDefault(key, DEFAULT_TRUST);
                    content.append("\n\tinit(trust_").append(mode).append("_").append(state.replace(" ", ""))
                           .append(") := ").append(trust).append(";");
                }
            }
        } else {
            if (smv.manifest != null && smv.manifest.getWorkingStates() != null) {
                for (DeviceManifest.WorkingState state : smv.manifest.getWorkingStates()) {
                    String trust = instanceTrust != null ? instanceTrust :
                            (state.getTrust() != null ? state.getTrust() : DEFAULT_TRUST);
                    content.append("\n\tinit(trust_").append(state.getName()).append(") := ").append(trust).append(";");
                }
            } else {
                for (String state : smv.states) {
                    String trust = instanceTrust != null ? instanceTrust :
                            smv.stateTrust.getOrDefault(state, DEFAULT_TRUST);
                    content.append("\n\tinit(trust_").append(state).append(") := ").append(trust).append(";");
                }
            }
        }

        for (DeviceManifest.InternalVariable var : smv.variables) {
            String instanceVarTrust = smv.instanceVariableTrust.get(var.getName());
            String trust = instanceVarTrust != null ? instanceVarTrust : (var.getTrust() != null ? var.getTrust() : DEFAULT_TRUST);
            if (isAttack && isSensor) {
                content.append("\n\tinit(trust_").append(var.getName()).append(") :=\n");
                content.append("\tcase\n");
                content.append("\t\tis_attack=TRUE: untrusted;\n");
                content.append("\t\tTRUE: ").append(trust).append(";\n");
                content.append("\tesac;");
            } else {
                content.append("\n\tinit(trust_").append(var.getName()).append(") := ").append(trust).append(";");
            }
        }
    }

    private void appendInitialPrivacy(StringBuilder content, DeviceSmvData smv, boolean isSensor) {
        List<String> modes = smv.modes;
        if (modes.size() > 1) {
            Set<String> initializedStates = new HashSet<>();
            if (smv.manifest != null && smv.manifest.getWorkingStates() != null) {
                for (DeviceManifest.WorkingState state : smv.manifest.getWorkingStates()) {
                    String[] mStates = state.getName().split(";");
                    for (int i = 0; i < modes.size() && i < mStates.length; i++) {
                        String stateKey = modes.get(i) + "_" + mStates[i].replace(" ", "");
                        if (initializedStates.contains(stateKey)) {
                            continue;
                        }
                        initializedStates.add(stateKey);
                        String instancePrivacy = smv.instanceVariablePrivacy.get(stateKey);
                        String privacy = instancePrivacy != null ? instancePrivacy :
                                (state.getPrivacy() != null ? state.getPrivacy() : DEFAULT_PRIVACY);
                        content.append("\n\tinit(privacy_").append(modes.get(i)).append("_").append(mStates[i].replace(" ", ""))
                               .append(") := ").append(privacy).append(";");
                    }
                }
            }
            for (String mode : modes) {
                List<String> states = smv.modeStates.get(mode);
                if (states == null) continue;
                for (String state : states) {
                    String stateKey = mode + "_" + state.replace(" ", "");
                    if (initializedStates.contains(stateKey)) continue;
                    initializedStates.add(stateKey);
                    String instancePrivacy = smv.instanceVariablePrivacy.get(stateKey);
                    String privacy = instancePrivacy != null ? instancePrivacy : DEFAULT_PRIVACY;
                    content.append("\n\tinit(privacy_").append(mode).append("_").append(state.replace(" ", ""))
                           .append(") := ").append(privacy).append(";");
                }
            }
        } else {
            if (smv.manifest != null && smv.manifest.getWorkingStates() != null) {
                for (DeviceManifest.WorkingState state : smv.manifest.getWorkingStates()) {
                    String instancePrivacy = smv.instanceVariablePrivacy.get(state.getName());
                    String privacy = instancePrivacy != null ? instancePrivacy :
                            (state.getPrivacy() != null ? state.getPrivacy() : DEFAULT_PRIVACY);
                    content.append("\n\tinit(privacy_").append(state.getName()).append(") := ").append(privacy).append(";");
                }
            } else {
                for (String state : smv.states) {
                    String instancePrivacy = smv.instanceVariablePrivacy.get(state);
                    String privacy = instancePrivacy != null ? instancePrivacy : DEFAULT_PRIVACY;
                    content.append("\n\tinit(privacy_").append(state).append(") := ").append(privacy).append(";");
                }
            }
        }

        for (DeviceManifest.InternalVariable var : smv.variables) {
            String instanceVarPrivacy = smv.instanceVariablePrivacy.get(var.getName());
            String privacy = instanceVarPrivacy != null ? instanceVarPrivacy : (var.getPrivacy() != null ? var.getPrivacy() : DEFAULT_PRIVACY);
            content.append("\n\tinit(privacy_").append(var.getName()).append(") := ").append(privacy).append(";");
        }
    }

    private void appendTransitions(StringBuilder content, DeviceSmvData smv, boolean isAttack, boolean isSensor) {
        if (smv.modes.size() <= 1) {
            appendStateTransitions(content, smv, isAttack, isSensor);
        } else {
            appendModeTransitions(content, smv, isAttack);
        }

        appendInternalVariableTransitions(content, smv, isAttack, isSensor);
        appendSignalVariableTransitions(content, smv, isAttack);
        appendVariableRateTransitions(content, smv);
    }

    private void appendStateTransitions(StringBuilder content, DeviceSmvData smv, boolean isAttack, boolean isSensor) {
        content.append("\n\tnext(state) := case\n");

        for (DeviceSmvData.TransitionInfo trans : smv.transitions) {
            if (trans.condition != null && !trans.condition.isEmpty()) {
                content.append("\t\t").append(trans.condition).append(": ").append(trans.nextState).append(";\n");
            }
        }

        for (String state : smv.states) {
            String selfLoop = "state = " + state;
            if (isSensor && isAttack) {
                selfLoop = "(" + selfLoop + " | is_attack)";
            }
            content.append("\t\t").append(selfLoop).append(": ").append(state).append(";\n");
        }

        content.append("\t\tTRUE: state;\n");
        content.append("\tesac;");
    }

    private void appendModeTransitions(StringBuilder content, DeviceSmvData smv, boolean isAttack) {
        content.append("\n");

        for (int i = 0; i < smv.modes.size(); i++) {
            String mode = smv.modes.get(i);

            content.append("\t-- Mode: ").append(mode).append("\n");
            content.append("\tnext(").append(mode).append(") := case\n");

            for (DeviceSmvData.TransitionInfo trans : smv.transitions) {
                String targetMode = extractTargetMode(trans.state);
                if (!mode.equals(targetMode)) continue;

                String nextState = trans.nextState;
                String condition = trans.condition;

                if (condition != null && !condition.isEmpty()) {
                    content.append("\t\t").append(condition)
                           .append(": ").append(nextState).append(";\n");
                }
            }

            content.append("\t\tTRUE: ").append(mode).append(";\n");
            content.append("\tesac;\n");
        }
    }

    private void appendInternalVariableTransitions(StringBuilder content, DeviceSmvData smv, boolean isAttack, boolean isSensor) {
        for (DeviceManifest.InternalVariable var : smv.variables) {
            if (var.getIsInside() == null || !var.getIsInside()) {
                appendExternalVariableAssignment(content, smv, var, isAttack, isSensor);
                continue;
            }

            content.append("\n\tnext(").append(var.getName()).append(") := case\n");

            if (isAttack && isSensor) {
                content.append("\t\tis_attack=TRUE: ");
                if (var.getValues() != null && !var.getValues().isEmpty()) {
                    content.append("{").append(String.join(", ", var.getValues())).append("};\n");
                } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                    content.append(var.getLowerBound()).append("..").append(var.getUpperBound()).append(";\n");
                } else {
                    content.append("0..100;\n");
                }
            }

            appendVariableDynamics(content, smv, var);

            content.append("\tesac;");
        }
    }

    private void appendExternalVariableAssignment(StringBuilder content, DeviceSmvData smv, 
                                                   DeviceManifest.InternalVariable var, boolean isAttack, boolean isSensor) {
        if (isAttack && isSensor) {
            content.append("\n\t").append(var.getName()).append(":= case\n");
            content.append("\t\tis_attack=TRUE: ");
            if (var.getValues() != null && !var.getValues().isEmpty()) {
                content.append("{").append(String.join(", ", var.getValues())).append("};\n");
            } else if (var.getLowerBound() != null && var.getUpperBound() != null) {
                content.append(var.getLowerBound()).append("..").append(var.getUpperBound()).append(";\n");
            } else {
                content.append("0..100;\n");
            }
            content.append("\t\tTRUE: a_").append(var.getName()).append(";\n");
            content.append("\tesac;\n");
        } else {
            content.append("\n\t").append(var.getName()).append(" := a_").append(var.getName()).append(";\n");
        }
    }

    private void appendVariableDynamics(StringBuilder content, DeviceSmvData smv, DeviceManifest.InternalVariable var) {
        List<String> modes = smv.modes;
        if (var.getValues() != null && !var.getValues().isEmpty()) {
            if (smv.impactedVariables != null && smv.impactedVariables.contains(var.getName())) {
                for (DeviceManifest.WorkingState state : smv.manifest.getWorkingStates()) {
                    if (state.getDynamics() == null || state.getDynamics().isEmpty()) continue;
                    for (DeviceManifest.Dynamic dynamic : state.getDynamics()) {
                        if (var.getName().equals(dynamic.getVariableName())) {
                            String[] states = state.getName().split(";");
                            content.append("\t\t");
                            for (int i = 0; i < modes.size() && i < states.length; i++) {
                                if (i > 0) content.append(" & ");
                                content.append(modes.get(i)).append("=").append(states[i].replace(" ", ""));
                            }
                            content.append(": ").append(dynamic.getValue()).append(";\n");
                        }
                    }
                }
            }
            content.append("\t\tTRUE: ").append(var.getName()).append(";\n");
        } else {
            appendNumericVariableTransitions(content, smv, var);
        }
    }

    private void appendNumericVariableTransitions(StringBuilder content, DeviceSmvData smv, DeviceManifest.InternalVariable var) {
        String impactedRate = "";
        if (smv.impactedVariables != null && smv.impactedVariables.contains(var.getName())) {
            impactedRate = var.getName() + "_rate";
        }

        String[] changeRate = var.getNaturalChangeRate() != null ? 
            var.getNaturalChangeRate().split("\\[|]|, ") : new String[]{"0"};

        if (changeRate.length == 1) {
            int rate = Integer.parseInt(changeRate[0]);
            if (rate > 0) {
                content.append("\t\t").append(var.getName()).append(">=").append(var.getUpperBound()).append(": ")
                       .append(var.getUpperBound()).append(";\n");
            } else if (rate < 0) {
                content.append("\t\t").append(var.getName()).append("<=").append(var.getLowerBound()).append(": ")
                       .append(var.getLowerBound()).append(";\n");
            }
            if (!impactedRate.isEmpty()) {
                content.append("\t\tTRUE: ").append(var.getName()).append("+").append(rate).append("+").append(impactedRate).append(";\n");
            } else {
                content.append("\t\tTRUE: ").append(var.getName()).append("+").append(rate).append(";\n");
            }
        } else {
            int lowerRate = Integer.parseInt(changeRate[1]);
            int upperRate = Integer.parseInt(changeRate[2]);
            
            if (lowerRate < 0) {
                content.append("\t\t").append(var.getName()).append("=").append(var.getUpperBound()).append(": {toint(")
                       .append(var.getName()).append(")").append(lowerRate);
                if (!impactedRate.isEmpty()) content.append("+").append(impactedRate);
                content.append(", ").append(var.getName());
                if (!impactedRate.isEmpty()) content.append("+").append(impactedRate);
                content.append("};\n");
                content.append("\t\t").append(var.getName()).append(">").append(var.getUpperBound()).append(": {")
                       .append(var.getUpperBound()).append("};\n");
            } else {
                content.append("\t\t").append(var.getName()).append(">=").append(var.getUpperBound()).append(": {")
                       .append(var.getUpperBound()).append("};\n");
            }
            
            if (upperRate > 0) {
                content.append("\t\t").append(var.getName()).append("=").append(var.getLowerBound()).append(": {")
                       .append(var.getName());
                if (!impactedRate.isEmpty()) content.append("+").append(impactedRate);
                content.append(", ").append(var.getName()).append("+").append(upperRate);
                if (!impactedRate.isEmpty()) content.append("+").append(impactedRate);
                content.append("};\n");
                content.append("\t\t").append(var.getName()).append("<").append(var.getLowerBound()).append(": {")
                       .append(var.getLowerBound()).append("};\n");
            } else {
                content.append("\t\t").append(var.getName()).append("<=").append(var.getLowerBound()).append(": {")
                       .append(var.getLowerBound()).append("};\n");
            }
            
            content.append("\t\tTRUE: {");
            if (lowerRate < 0) {
                content.append(var.getName()).append("+").append(lowerRate);
                if (!impactedRate.isEmpty()) content.append("+").append(impactedRate);
                content.append(", ");
            }
            content.append(var.getName());
            if (!impactedRate.isEmpty()) content.append("+").append(impactedRate);
            if (upperRate > 0) {
                content.append(", ").append(var.getName()).append("+").append(upperRate);
                if (!impactedRate.isEmpty()) content.append("+").append(impactedRate);
            }
            content.append("};\n");
        }
    }

    private void appendSignalVariableTransitions(StringBuilder content, DeviceSmvData smv, boolean isAttack) {
        for (DeviceSmvData.SignalInfo sig : smv.signalVars) {
            if (sig.getType() != null && API_SIGNAL_TYPE.equals(sig.getType())) {
                content.append("\n\tnext(").append(sig.getName()).append(") :=\ncase\n");

                String startState = sig.getStart();
                String endState = sig.getEnd();

                if (smv.modes != null && smv.modes.size() > 1) {
                    for (String mode : smv.modes) {
                        if (startState != null && startState.contains(mode)) {
                            content.append("\t\t").append(mode).append(" != ").append(endState)
                                   .append(" & next(").append(mode).append(") = ").append(endState).append(": TRUE;\n");
                        }
                    }
                } else if (!smv.states.isEmpty()) {
                    if (startState != null && smv.states.contains(startState)) {
                        content.append("\t\tstate = ").append(startState)
                               .append(" & next(state) = ").append(endState).append(": TRUE;\n");
                    }
                }

                content.append("\t\tTRUE: FALSE;\n");
                content.append("\tesac;");
            }
        }
    }

    private void appendVariableRateTransitions(StringBuilder content, DeviceSmvData smv) {
        for (String varName : smv.impactedVariables) {
            content.append("\n\tnext(").append(varName).append("_rate) :=\ncase\n");

            for (String mode : smv.modes) {
                List<String> states = smv.modeStates.get(mode);
                if (states == null) continue;

                for (String state : states) {
                    Map<String, String> dynamics = smv.stateDynamics.get(mode + "_" + state);
                    if (dynamics != null && dynamics.containsKey(varName)) {
                        String rate = dynamics.get(varName);
                        content.append("\t\t").append(mode).append(" = ").append(state).append(": ").append(rate).append(";\n");
                    }
                }
            }

            content.append("\t\tTRUE: 0;\n");
            content.append("\tesac;");
        }
    }

    private String extractTargetMode(String stateName) {
        if (stateName == null) return "";
        int underscoreIndex = stateName.indexOf('_');
        if (underscoreIndex > 0) {
            return stateName.substring(0, underscoreIndex);
        }
        return "";
    }
}
