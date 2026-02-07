package cn.edu.nju.Iot_Verify.component.nusmv.data;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import lombok.Data;

import java.util.*;

@Data
public class DeviceSmvData {
    // 设备基本信息
    public String id;
    public String name;
    public int deviceNo;

    // 静态结构（从模板加载）
    public List<String> states = new ArrayList<>();
    public List<DeviceManifest.InternalVariable> variables = new ArrayList<>();
    public List<TransitionInfo> transitions = new ArrayList<>();

    // 多模式支持
    public List<String> modes = new ArrayList<>();
    public Map<String, List<String>> modeStates = new LinkedHashMap<>();
    public Map<String, String> modeStateTrust = new LinkedHashMap<>();

    // 信号变量
    public List<SignalInfo> signalVars = new ArrayList<>();

    // 运行时状态（从设备实例加载）
    public String currentState;
    public Map<String, String> currentModeStates = new LinkedHashMap<>();
    public String currentStateTrust;
    public Map<String, String> variableValues = new HashMap<>();

    // 实例级信任和隐私（从设备实例加载）
    public String instanceStateTrust;
    public Map<String, String> instanceVariableTrust = new HashMap<>();
    public Map<String, String> instanceVariablePrivacy = new HashMap<>();

    // 信任和隐私映射
    public Map<String, String> stateTrust = new HashMap<>();
    public Map<String, String> contentPrivacy = new HashMap<>();

    // 变量变化率
    public List<String> impactedVariables = new ArrayList<>();

    // 隐私内容
    public List<ContentInfo> contents = new ArrayList<>();

    // 变量动态信息
    public Map<String, Map<String, String>> stateDynamics = new HashMap<>();

    // 环境变量映射
    public Map<String, DeviceManifest.InternalVariable> envVariables = new HashMap<>();

    // 受影响的变量-设备映射
    public Map<String, List<String>> impactVariableDevice = new HashMap<>();

    // 模板 Manifest 引用（用于获取 Transitions 和 APIs）
    public transient DeviceManifest manifest;

    /**
     * 获取模块名称，用于 NuSMV MODULE 定义
     * @return 安全的模块名称（移除特殊字符，如果结果为空则使用默认值）
     */
    public String getModuleName() {
        String templateName = name != null ? name : "Device";
        String result = templateName.replaceAll("[^a-zA-Z0-9]", "");
        if (result.isEmpty()) {
            result = "Device_" + deviceNo;
        }
        return result;
    }

    /**
     * 获取变量名称，用于 NuSMV 变量引用
     * @return 安全的变量名称
     */
    public String getVarName() {
        String safeId = id != null ? id.replaceAll("[^a-zA-Z0-9_]", "_") : "_";
        // 转换为小写，但确保不全部是下划线
        String result = safeId.toLowerCase();
        if (result.isEmpty() || result.matches("^_+$")) {
            result = "device_" + deviceNo;
        }
        return result;
    }

    /**
     * 静态工具方法：将设备 ID 转换为安全的变量名称
     * @param deviceId 设备 ID
     * @return 安全的变量名称
     */
    public static String getVarNameForId(String deviceId) {
        if (deviceId == null) {
            return "device";
        }
        return deviceId.replaceAll("[^a-zA-Z0-9_]", "_").toLowerCase();
    }

    @Data
    public static class SignalInfo {
        public String name;
        public String start;
        public String end;
        public String trigger;
        public String type;
    }

    @Data
    public static class ContentInfo {
        public String name;
        public String privacy;
        public Boolean isChangeable;
    }

    @Data
    public static class TransitionInfo {
        public String state;
        public String nextState;
        public String condition;
        public int ruleNo;
        public String nextValue;
        public String transitionName;
    }
}
