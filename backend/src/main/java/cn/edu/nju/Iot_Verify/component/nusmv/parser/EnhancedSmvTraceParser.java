package cn.edu.nju.Iot_Verify.component.nusmv.parser;

import cn.edu.nju.Iot_Verify.component.nusmv.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.trace.*;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * 增强版 SMV Trace 解析器
 * 
 * 支持多种 NuSMV 输出格式：
 * 1. 标准 NuSMV counterexample 格式
 * 2. MEDIC-test 输出格式
 * 3. 简单状态序列格式
 * 
 * 可以解析文件或字符串输入
 */
@Slf4j
@Component
public class EnhancedSmvTraceParser {

    // 标准 NuSMV 格式: State 1.x:
    private static final Pattern STANDARD_STATE_PATTERN = 
        Pattern.compile("State\\s+1\\.(\\d+):");
    
    // MEDIC-test 格式: -- At time N: ... State 1.x:
    private static final Pattern MEDIC_TIME_PATTERN = 
        Pattern.compile("-- At time (\\d+):");
    
    // 变量赋值: device_var.attr = value 或 device.attr = value
    private static final Pattern VAR_ASSIGNMENT_PATTERN = 
        Pattern.compile("(\\w+)[_.](\\w+)\\s*=\\s*(\\S+)");
    
    // 输入信号: -> Input: signal = value
    private static final Pattern INPUT_SIGNAL_PATTERN = 
        Pattern.compile("->\\s*Input:\\s*(\\w+)\\s*=\\s*(\\w+)");
    
    // 循环指示: -- Loop starts here
    private static final Pattern LOOP_PATTERN = 
        Pattern.compile("--\\s*Loop starts here");
    
    // 状态描述: State 1.x: StateName
    private static final Pattern STATE_NAME_PATTERN = 
        Pattern.compile("State\\s+1\\.(\\d+):\\s*(\\w+)");

    /**
     * 从文件解析 NuSMV 输出
     * 
     * @param outputFile NuSMV 输出文件
     * @param deviceSmvMap 设备映射信息
     * @return 状态序列列表
     */
    public List<TraceStateDto> parseFromFile(File outputFile, Map<String, DeviceSmvData> deviceSmvMap) 
            throws IOException {
        if (!outputFile.exists()) {
            throw new IOException("Output file does not exist: " + outputFile.getAbsolutePath());
        }
        
        String content = Files.readString(outputFile.toPath());
        return parse(content, deviceSmvMap);
    }

    /**
     * 从字符串解析 NuSMV 输出（自动检测格式）
     * 
     * @param content NuSMV 输出内容
     * @param deviceSmvMap 设备映射信息
     * @return 状态序列列表
     */
    public List<TraceStateDto> parse(String content, Map<String, DeviceSmvData> deviceSmvMap) {
        if (content == null || content.trim().isEmpty()) {
            log.warn("Empty content provided for parsing");
            return Collections.emptyList();
        }

        // 检测格式类型
        FormatType formatType = detectFormat(content);
        log.debug("Detected format type: {}", formatType);

        switch (formatType) {
            case MEDIC:
                return parseMedicFormat(content, deviceSmvMap);
            case STANDARD:
                return parseStandardFormat(content, deviceSmvMap);
            case SIMPLE:
            default:
                return parseSimpleFormat(content, deviceSmvMap);
        }
    }

    /**
     * 检测 NuSMV 输出格式类型
     */
    private FormatType detectFormat(String content) {
        if (content.contains("MEDIC") || content.contains("-- At time")) {
            return FormatType.MEDIC;
        } else if (content.contains("Trace Description") || content.contains("Trace Type")) {
            return FormatType.STANDARD;
        } else {
            return FormatType.SIMPLE;
        }
    }

    /**
     * 解析 MEDIC-test 格式
     * 
     * 格式示例：
     * -- At time 0:
     * State 1.1:
     * -> Input: toggle_ac_1 = TRUE
     *    ac_1.state = Off
     *    ac_1.temperature = 24
     * -- At time 1:
     * State 1.2:
     *    ac_1.state = Cooling
     */
    private List<TraceStateDto> parseMedicFormat(String content, Map<String, DeviceSmvData> deviceSmvMap) {
        List<TraceStateDto> states = new ArrayList<>();
        
        String[] lines = content.split("\n");
        TraceStateDto currentState = null;
        int currentStateIndex = 0;
        List<String> currentInputs = new ArrayList<>();
        
        for (int i = 0; i < lines.length; i++) {
            String line = lines[i].trim();
            
            if (line.isEmpty() || line.startsWith("--") && !line.contains("At time")) {
                continue;
            }

            // 检测时间标记
            Matcher timeMatcher = MEDIC_TIME_PATTERN.matcher(line);
            if (timeMatcher.find()) {
                // 保存上一个状态
                if (currentState != null) {
                    states.add(currentState);
                }
                
                currentState = new TraceStateDto();
                currentState.setStateIndex(currentStateIndex++);
                currentState.setDevices(new ArrayList<>());
                currentInputs = new ArrayList<>();
                continue;
            }

            // 检测状态行
            Matcher stateMatcher = STANDARD_STATE_PATTERN.matcher(line);
            if (stateMatcher.find()) {
                int stateIdx = Integer.parseInt(stateMatcher.group(1));
                if (currentState == null) {
                    currentState = new TraceStateDto();
                    currentState.setStateIndex(stateIdx - 1);
                    currentState.setDevices(new ArrayList<>());
                }
                continue;
            }

            // 检测输入信号
            Matcher inputMatcher = INPUT_SIGNAL_PATTERN.matcher(line);
            if (inputMatcher.find() && currentState != null) {
                String signal = inputMatcher.group(1);
                String value = inputMatcher.group(2);
                currentInputs.add(signal + "=" + value);
                continue;
            }

            // 解析变量赋值
            if (currentState != null) {
                parseVariableLine(line, currentState, deviceSmvMap);
            }
        }

        // 添加最后一个状态
        if (currentState != null) {
            states.add(currentState);
        }

        log.info("Parsed {} states from MEDIC format", states.size());
        return states;
    }

    /**
     * 解析标准 NuSMV 格式
     * 
     * 格式示例：
     * -- Trace Description: CTL Counterexample
     * -- Trace Type: Counterexample
     * --
     * State 1.1:
     *   ac_1.state = Off
     * State 1.2:
     *   ac_1.state = Cooling
     * -- Loop starts here
     */
    private List<TraceStateDto> parseStandardFormat(String content, Map<String, DeviceSmvData> deviceSmvMap) {
        List<TraceStateDto> states = new ArrayList<>();
        
        String[] lines = content.split("\n");
        TraceStateDto currentState = null;
        boolean inTraceSection = false;
        
        for (String line : lines) {
            String trimmed = line.trim();
            
            // 检测 Trace 开始
            if (trimmed.contains("Trace Description") || trimmed.contains("Trace Type")) {
                inTraceSection = true;
                continue;
            }
            
            if (!inTraceSection) {
                continue;
            }

            // 检测状态行
            Matcher stateMatcher = STANDARD_STATE_PATTERN.matcher(trimmed);
            if (stateMatcher.find()) {
                if (currentState != null) {
                    states.add(currentState);
                }
                
                currentState = new TraceStateDto();
                currentState.setStateIndex(Integer.parseInt(stateMatcher.group(1)) - 1);
                currentState.setDevices(new ArrayList<>());
                continue;
            }

            // 检测循环
            if (LOOP_PATTERN.matcher(trimmed).find() && currentState != null) {
                // 可以在这里标记循环起点
                continue;
            }

            // 解析变量
            if (currentState != null) {
                parseVariableLine(trimmed, currentState, deviceSmvMap);
            }
        }

        if (currentState != null) {
            states.add(currentState);
        }

        log.info("Parsed {} states from standard format", states.size());
        return states;
    }

    /**
     * 解析简单格式（兼容旧版本）
     */
    private List<TraceStateDto> parseSimpleFormat(String content, Map<String, DeviceSmvData> deviceSmvMap) {
        List<TraceStateDto> states = new ArrayList<>();
        
        String[] lines = content.split("\n");
        TraceStateDto currentState = null;
        
        for (String line : lines) {
            String trimmed = line.trim();
            if (trimmed.isEmpty()) {
                continue;
            }

            Matcher stateMatcher = STANDARD_STATE_PATTERN.matcher(trimmed);
            if (stateMatcher.find()) {
                if (currentState != null) {
                    states.add(currentState);
                }
                
                currentState = new TraceStateDto();
                currentState.setStateIndex(Integer.parseInt(stateMatcher.group(1)) - 1);
                currentState.setDevices(new ArrayList<>());
                continue;
            }

            if (currentState != null) {
                parseVariableLine(trimmed, currentState, deviceSmvMap);
            }
        }

        if (currentState != null) {
            states.add(currentState);
        }

        log.info("Parsed {} states from simple format", states.size());
        return states;
    }

    /**
     * 解析变量赋值行
     */
    private void parseVariableLine(String line, TraceStateDto state, Map<String, DeviceSmvData> deviceSmvMap) {
        Matcher varMatcher = VAR_ASSIGNMENT_PATTERN.matcher(line);
        
        while (varMatcher.find()) {
            String deviceId = varMatcher.group(1);
            String attr = varMatcher.group(2);
            String value = varMatcher.group(3).replace(";", "").trim();
            
            DeviceSmvData deviceData = findDeviceData(deviceSmvMap, deviceId);
            if (deviceData == null) {
                log.warn("Device not found for id: {}", deviceId);
                continue;
            }

            TraceDeviceDto deviceTrace = findOrCreateDeviceTrace(state, deviceData.id);
            deviceTrace.setDeviceLabel(deviceData.name);
            deviceTrace.setTemplateName(deviceData.name);
            
            if ("state".equals(attr)) {
                String matchedState = matchState(deviceData, value);
                deviceTrace.setNewState(matchedState != null ? matchedState : value);
            } else {
                if (deviceTrace.getVariables() == null) {
                    deviceTrace.setVariables(new ArrayList<>());
                }
                
                TraceVariableDto var = new TraceVariableDto();
                var.setName(attr);
                var.setValue(value);
                var.setTrust("trusted"); // 默认值
                deviceTrace.getVariables().add(var);
            }
        }
    }

    /**
     * 查找设备数据
     */
    private DeviceSmvData findDeviceData(Map<String, DeviceSmvData> deviceSmvMap, String deviceId) {
        if (deviceSmvMap == null) {
            return null;
        }

        // 直接匹配
        DeviceSmvData direct = deviceSmvMap.get(deviceId);
        if (direct != null) {
            return direct;
        }

        // 尝试去掉后缀匹配
        for (DeviceSmvData data : deviceSmvMap.values()) {
            if (deviceId.startsWith(data.name) || data.name.startsWith(deviceId)) {
                return data;
            }
            if (deviceId.contains("_")) {
                String base = deviceId.substring(0, deviceId.lastIndexOf('_'));
                if (base.equals(data.name)) {
                    return data;
                }
            }
        }

        return null;
    }

    /**
     * 查找或创建设备跟踪
     */
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

    /**
     * 匹配状态名称
     */
    private String matchState(DeviceSmvData smv, String value) {
        if (value == null || smv.states == null) {
            return null;
        }

        for (String state : smv.states) {
            if (state.equalsIgnoreCase(value)) {
                return state;
            }
        }

        // 尝试模式匹配
        for (String mode : smv.modes) {
            String modeState = mode + "_" + value;
            if (smv.states.contains(modeState)) {
                return modeState;
            }
        }

        return null;
    }

    /**
     * 格式类型枚举
     */
    private enum FormatType {
        MEDIC,      // MEDIC-test 格式
        STANDARD,   // 标准 NuSMV 格式
        SIMPLE      // 简单格式
    }

    /**
     * 解析结果封装
     */
    public static class ParseResult {
        private final List<TraceStateDto> states;
        private final boolean hasLoop;
        private final int loopStartIndex;
        private final Map<String, Object> metadata;

        public ParseResult(List<TraceStateDto> states, boolean hasLoop, int loopStartIndex, 
                          Map<String, Object> metadata) {
            this.states = states;
            this.hasLoop = hasLoop;
            this.loopStartIndex = loopStartIndex;
            this.metadata = metadata;
        }

        public List<TraceStateDto> getStates() { return states; }
        public boolean hasLoop() { return hasLoop; }
        public int getLoopStartIndex() { return loopStartIndex; }
        public Map<String, Object> getMetadata() { return metadata; }
    }
}
