package cn.edu.nju.Iot_Verify.component.nusmv.parser;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDeviceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceTrustPrivacyDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceVariableDto;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * SMV Trace parser.
 * Parse NuSMV counterexample output into TraceStateDto list.
 */
@Component
public class SmvTraceParser {

    // Compatible with "State 1.1:" and "-> State: 1.1 <-"
    // Anchored to line start (^\s*) to prevent mid-line false matches
    private static final Pattern STATE_PATTERN =
            Pattern.compile("^\\s*(?:->\\s*)?State[:\\s]\\s*\\d+\\.(\\d+)(?:\\s*<-|:)?\\s*(\\w+)?");
    private static final Pattern STATE_LINE_PATTERN =
            Pattern.compile("^\\s*(?:->\\s*)?State[:\\s]\\s*\\d+\\.(\\d+)");
    private static final Pattern VAR_PATTERN =
            Pattern.compile("(\\w+)\\.(\\w+)\\s*=\\s*(\\S+)");
    private static final Pattern ENV_VAR_PATTERN =
            Pattern.compile("^(a_\\w+)\\s*=\\s*(\\S+)$");

    public List<TraceStateDto> parseCounterexampleStates(String counterexample,
                                                         Map<String, DeviceSmvData> deviceSmvMap) {
        List<TraceStateDto> states = new ArrayList<>();
        if (counterexample == null || counterexample.isEmpty()) {
            return states;
        }

        String[] lines = counterexample.split("\n");
        TraceStateDto currentState = null;
        String pendingStateName = null;
        Map<String, Map<String, String>> previousModeValuesByDevice = new HashMap<>();

        for (String line : lines) {
            line = line.trim();
            if (line.isEmpty()) {
                continue;
            }

            Matcher stateMatcher = STATE_LINE_PATTERN.matcher(line);
            if (stateMatcher.find()) {
                int stateIdx = Integer.parseInt(stateMatcher.group(1));
                if (currentState != null) {
                    finalizeModeStates(currentState, deviceSmvMap, previousModeValuesByDevice);
                    states.add(currentState);
                }

                currentState = new TraceStateDto();
                currentState.setStateIndex(stateIdx);
                currentState.setDevices(new ArrayList<>());

                Matcher stateNameMatcher = STATE_PATTERN.matcher(line);
                if (stateNameMatcher.find() && stateNameMatcher.group(2) != null) {
                    pendingStateName = stateNameMatcher.group(2);
                } else {
                    pendingStateName = null;
                }

                parseLineVariables(currentState, line, deviceSmvMap, pendingStateName);
                continue;
            }

            if (currentState != null) {
                parseLineVariables(currentState, line, deviceSmvMap, pendingStateName);
            }
        }

        if (currentState != null) {
            finalizeModeStates(currentState, deviceSmvMap, previousModeValuesByDevice);
            states.add(currentState);
        }
        return states;
    }

    private void parseLineVariables(TraceStateDto currentState,
                                    String line,
                                    Map<String, DeviceSmvData> deviceSmvMap,
                                    String pendingStateName) {
        Matcher varMatcher = VAR_PATTERN.matcher(line);
        while (varMatcher.find()) {
            processVariable(currentState,
                    varMatcher.group(1),
                    varMatcher.group(2),
                    varMatcher.group(3),
                    deviceSmvMap,
                    pendingStateName);
        }

        Matcher envMatcher = ENV_VAR_PATTERN.matcher(line);
        while (envMatcher.find()) {
            processEnvVariable(currentState, envMatcher.group(1), envMatcher.group(2));
        }
    }

    private void processVariable(TraceStateDto state,
                                 String deviceId,
                                 String attr,
                                 String value,
                                 Map<String, DeviceSmvData> deviceSmvMap,
                                 String stateName) {
        if (deviceId == null || attr == null || value == null) {
            return;
        }

        String cleanValue = value.replace(";", "").trim();
        DeviceSmvData smv = findDeviceByIdOrName(deviceSmvMap, deviceId);
        if (smv == null) {
            return;
        }

        TraceDeviceDto devTrace = findOrCreateDeviceTrace(state, deviceId);
        if (devTrace.getTemplateName() == null) {
            devTrace.setTemplateName(smv.getTemplateName());
        }
        if (devTrace.getDeviceLabel() == null) {
            devTrace.setDeviceLabel(smv.getVarName() != null ? smv.getVarName() : deviceId);
        }
        if (devTrace.getState() == null && stateName != null) {
            String matchedState = matchState(smv, stateName);
            devTrace.setState(matchedState != null ? matchedState : stateName);
            if (devTrace.getMode() == null && smv.getModes() != null && smv.getModes().size() == 1) {
                devTrace.setMode(smv.getModes().get(0));
            }
        }

        // Legacy parser compatibility.
        if ("state".equals(attr)) {
            String matchedState = matchState(smv, cleanValue);
            devTrace.setState(matchedState != null ? matchedState : cleanValue);
            if (devTrace.getMode() == null && smv.getModes() != null && smv.getModes().size() == 1) {
                devTrace.setMode(smv.getModes().get(0));
            }
            return;
        }

        // NuSMV state variable name is mode name (e.g. HvacMode / SwitchState).
        if (smv.getModes() != null && smv.getModes().contains(attr)) {
            TraceVariableDto modeVar = findOrCreateVariable(devTrace, "__mode__" + attr);
            modeVar.setValue(cleanValue);
            return;
        }

        if (attr.startsWith("trust_")) {
            processTrustVariable(devTrace, smv, attr.substring("trust_".length()), cleanValue);
            return;
        }

        if (attr.startsWith("privacy_")) {
            TraceTrustPrivacyDto privacy = findOrCreateTrustPrivacy(devTrace, false, attr.substring("privacy_".length()));
            privacy.setPrivacy(cleanValue);
            return;
        }

        if (isInternalControlVariable(attr)) {
            return;
        }

        TraceVariableDto varTrace = findOrCreateVariable(devTrace, attr);
        varTrace.setValue(cleanValue);
    }

    private void processEnvVariable(TraceStateDto state, String name, String value) {
        if (state == null || name == null || value == null) {
            return;
        }
        if (!name.startsWith("a_")) {
            return;
        }

        if (state.getEnvVariables() == null) {
            state.setEnvVariables(new ArrayList<>());
        }

        String cleanValue = value.replace(";", "").trim();
        for (TraceVariableDto envVar : state.getEnvVariables()) {
            if (name.equals(envVar.getName())) {
                envVar.setValue(cleanValue);
                return;
            }
        }

        TraceVariableDto created = new TraceVariableDto();
        created.setName(name);
        created.setValue(cleanValue);
        state.getEnvVariables().add(created);
    }

    private void processTrustVariable(TraceDeviceDto devTrace,
                                      DeviceSmvData smv,
                                      String targetName,
                                      String value) {
        if (targetName == null || targetName.isBlank()) {
            return;
        }

        boolean modeTrust = false;
        if (smv.getModes() != null) {
            for (String mode : smv.getModes()) {
                if (targetName.startsWith(mode + "_")) {
                    String stateName = targetName.substring((mode + "_").length());
                    List<String> modeStates = smv.getModeStates() != null ? smv.getModeStates().get(mode) : null;
                    if (modeStates != null && modeStates.contains(stateName)) {
                        modeTrust = true;
                        break;
                    }
                }
            }
        }

        if (modeTrust) {
            TraceTrustPrivacyDto trust = findOrCreateTrustPrivacy(devTrace, true, targetName);
            trust.setTrust("trusted".equals(value));
            return;
        }

        TraceVariableDto variable = findOrCreateVariable(devTrace, targetName);
        variable.setTrust(value);
    }

    private boolean isInternalControlVariable(String attr) {
        return "is_attack".equals(attr) || attr.endsWith("_rate") || attr.endsWith("_a");
    }

    private TraceVariableDto findOrCreateVariable(TraceDeviceDto devTrace, String name) {
        if (devTrace.getVariables() == null) {
            devTrace.setVariables(new ArrayList<>());
        }

        for (TraceVariableDto var : devTrace.getVariables()) {
            if (name.equals(var.getName())) {
                return var;
            }
        }

        TraceVariableDto created = new TraceVariableDto();
        created.setName(name);
        devTrace.getVariables().add(created);
        return created;
    }

    private TraceVariableDto findVariable(TraceDeviceDto devTrace, String name) {
        if (devTrace.getVariables() == null) {
            return null;
        }
        for (TraceVariableDto var : devTrace.getVariables()) {
            if (name.equals(var.getName())) {
                return var;
            }
        }
        return null;
    }

    private TraceTrustPrivacyDto findOrCreateTrustPrivacy(TraceDeviceDto devTrace,
                                                          boolean trustList,
                                                          String name) {
        List<TraceTrustPrivacyDto> list = trustList ? devTrace.getTrustPrivacy() : devTrace.getPrivacies();
        if (list == null) {
            list = new ArrayList<>();
            if (trustList) {
                devTrace.setTrustPrivacy(list);
            } else {
                devTrace.setPrivacies(list);
            }
        }

        for (TraceTrustPrivacyDto item : list) {
            if (name.equals(item.getName())) {
                return item;
            }
        }

        TraceTrustPrivacyDto created = new TraceTrustPrivacyDto();
        created.setName(name);
        list.add(created);
        return created;
    }

    private void finalizeModeStates(TraceStateDto state,
                                    Map<String, DeviceSmvData> deviceSmvMap,
                                    Map<String, Map<String, String>> previousModeValuesByDevice) {
        if (state == null || state.getDevices() == null) {
            return;
        }

        for (TraceDeviceDto dev : state.getDevices()) {
            DeviceSmvData smv = findDeviceByIdOrName(deviceSmvMap, dev.getDeviceId());
            if (smv == null || smv.getModes() == null || smv.getModes().isEmpty()) {
                continue;
            }

            Map<String, String> previousModeValues =
                    previousModeValuesByDevice.computeIfAbsent(dev.getDeviceId(), k -> new HashMap<>());
            List<String> modeValues = new ArrayList<>();
            List<String> modeNames = new ArrayList<>();
            boolean hasAnyModeValue = false;
            boolean hasAllModeValues = true;
            for (String mode : smv.getModes()) {
                TraceVariableDto modeVar = findVariable(dev, "__mode__" + mode);
                String modeValue = null;
                if (modeVar != null && modeVar.getValue() != null && !modeVar.getValue().isBlank()) {
                    modeValue = modeVar.getValue();
                    previousModeValues.put(mode, modeValue);
                } else {
                    modeValue = previousModeValues.get(mode);
                }

                if (modeValue != null && !modeValue.isBlank()) {
                    hasAnyModeValue = true;
                    modeValues.add(modeValue);
                    modeNames.add(mode);
                } else {
                    hasAllModeValues = false;
                }
            }

            if (hasAnyModeValue) {
                if (smv.getModes().size() > 1 && hasAllModeValues) {
                    dev.setState(String.join(";", modeValues));
                    dev.setMode(String.join(";", smv.getModes()));
                } else if (smv.getModes().size() == 1) {
                    dev.setState(modeValues.get(0));
                    dev.setMode(modeNames.get(0));
                } else if (dev.getState() == null || dev.getState().isBlank()) {
                    // 部分 mode 有值：用实际可用的 mode/value 对
                    dev.setState(modeValues.get(0));
                    dev.setMode(modeNames.get(0));
                }
            }

            // state 已由早期路径设置但 mode 仍为空时，尝试回填
            if (dev.getMode() == null && smv.getModes() != null) {
                if (smv.getModes().size() == 1) {
                    dev.setMode(smv.getModes().get(0));
                } else if (!modeNames.isEmpty()) {
                    dev.setMode(modeNames.get(0));
                }
            }

            if (dev.getVariables() != null) {
                dev.getVariables().removeIf(v -> v.getName() != null && v.getName().startsWith("__mode__"));
                if (dev.getVariables().isEmpty()) {
                    dev.setVariables(null);
                }
            }
        }
    }

    private DeviceSmvData findDeviceByIdOrName(Map<String, DeviceSmvData> deviceSmvMap, String id) {
        if (deviceSmvMap == null) {
            return null;
        }

        DeviceSmvData directMatch = deviceSmvMap.get(id);
        if (directMatch != null) {
            return directMatch;
        }

        for (DeviceSmvData smv : deviceSmvMap.values()) {
            if (id.equals(smv.getVarName())) {
                return smv;
            }
        }

        for (DeviceSmvData smv : deviceSmvMap.values()) {
            if (smv.getTemplateName() != null && smv.getTemplateName().equals(id)) {
                return smv;
            }
        }
        return null;
    }

    private TraceDeviceDto findOrCreateDeviceTrace(TraceStateDto state, String deviceId) {
        if (state.getDevices() == null) {
            state.setDevices(new ArrayList<>());
        }

        for (TraceDeviceDto dev : state.getDevices()) {
            if (deviceId.equals(dev.getDeviceId())) {
                return dev;
            }
        }

        TraceDeviceDto newDev = new TraceDeviceDto();
        newDev.setDeviceId(deviceId);
        state.getDevices().add(newDev);
        return newDev;
    }

    private String matchState(DeviceSmvData smv, String value) {
        if (value == null || smv.getStates() == null) {
            return null;
        }
        String cleanValue = DeviceSmvDataFactory.cleanStateName(value);

        for (String state : smv.getStates()) {
            if (state.equals(value) || state.equals(cleanValue)) {
                return state;
            }
        }

        if (smv.getModes() != null) {
            for (String mode : smv.getModes()) {
                String modeState = mode + "_" + cleanValue;
                if (smv.getStates().contains(modeState)) {
                    return modeState;
                }
            }
        }

        return null;
    }
}
