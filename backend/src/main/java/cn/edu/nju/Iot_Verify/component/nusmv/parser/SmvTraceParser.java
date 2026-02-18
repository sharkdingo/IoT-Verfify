package cn.edu.nju.Iot_Verify.component.nusmv.parser;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.trace.*;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * SMV Trace 解析器
 * 职责：解析 NuSMV 输出的 counterexample 为 TraceDto
 */
@Slf4j
@Component
public class SmvTraceParser {

    // 兼容旧格式 "State 1.1:" 和 NuSMV 2.7.1 格式 "-> State: 1.1 <-"
    private static final Pattern STATE_PATTERN = Pattern.compile("(?:->\\s*)?State[:\\s]\\s*1\\.(\\d+)(?:\\s*<-|:)?\\s*(\\w+)?");
    private static final Pattern STATE_LINE_PATTERN = Pattern.compile("(?:->\\s*)?State[:\\s]\\s*1\\.(\\d+)");
    private static final Pattern VAR_PATTERN = Pattern.compile("(\\w+)\\.(\\w+)\\s*=\\s*(\\S+)");

    public List<TraceStateDto> parseCounterexampleStates(String counterexample, Map<String, DeviceSmvData> deviceSmvMap) {
        List<TraceStateDto> states = new ArrayList<>();

        if (counterexample == null || counterexample.isEmpty()) {
            return states;
        }

        String[] lines = counterexample.split("\n");
        TraceStateDto currentState = null;
        String pendingStateName = null;

        for (String line : lines) {
            line = line.trim();
            if (line.isEmpty()) {
                continue;
            }

            Matcher stateMatcher = STATE_LINE_PATTERN.matcher(line);
            if (stateMatcher.find()) {
                int stateIdx = Integer.parseInt(stateMatcher.group(1));

                if (currentState != null) {
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

                Matcher varMatcher = VAR_PATTERN.matcher(line);
                while (varMatcher.find()) {
                    processVariable(currentState, varMatcher.group(1), varMatcher.group(2), varMatcher.group(3), deviceSmvMap, pendingStateName);
                }
                continue;
            }

            Matcher varMatcher = VAR_PATTERN.matcher(line);
            while (varMatcher.find()) {
                if (currentState != null) {
                    processVariable(currentState, varMatcher.group(1), varMatcher.group(2), varMatcher.group(3), deviceSmvMap, pendingStateName);
                }
            }
        }

        if (currentState != null) {
            states.add(currentState);
        }

        return states;
    }

    private void processVariable(TraceStateDto state, String deviceId, String attr, String value, Map<String, DeviceSmvData> deviceSmvMap, String stateName) {
        if (deviceId == null || attr == null || value == null) {
            return;
        }

        value = value.replace(";", "").trim();

        if ("state".equals(attr)) {
            DeviceSmvData smv = findDeviceByIdOrName(deviceSmvMap, deviceId);
            if (smv != null) {
                TraceDeviceDto devTrace = findOrCreateDeviceTrace(state, deviceId);

                String matchedState = matchState(smv, value);
                if (matchedState != null) {
                    devTrace.setNewState(matchedState);
                } else {
                    devTrace.setNewState(value);
                }
            }
        } else {
            DeviceSmvData smv = findDeviceByIdOrName(deviceSmvMap, deviceId);
            if (smv != null) {
                TraceDeviceDto devTrace = findOrCreateDeviceTrace(state, deviceId);
                
                if (devTrace.getNewState() == null && stateName != null) {
                    String matchedState = matchState(smv, stateName);
                    devTrace.setNewState(matchedState != null ? matchedState : stateName);
                }
                
                if (devTrace.getVariables() == null) {
                    devTrace.setVariables(new ArrayList<>());
                }
                TraceVariableDto varTrace = new TraceVariableDto();
                varTrace.setName(attr);
                varTrace.setValue(value);
                devTrace.getVariables().add(varTrace);
            }
        }
    }

    private DeviceSmvData findDeviceByIdOrName(Map<String, DeviceSmvData> deviceSmvMap, String id) {
        if (deviceSmvMap == null) {
            return null;
        }

        // 直接按 key 查找（varName 或 templateName）
        DeviceSmvData directMatch = deviceSmvMap.get(id);
        if (directMatch != null) {
            return directMatch;
        }

        // 按 varName（NuSMV 输出中的实际变量名）匹配
        for (DeviceSmvData smv : deviceSmvMap.values()) {
            if (id.equals(smv.getVarName())) {
                return smv;
            }
        }

        // 按 templateName 匹配
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
