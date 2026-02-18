package cn.edu.nju.Iot_Verify.component.nusmv.generator.data;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import lombok.Data;

import java.util.*;

/**
 * 设备 SMV 数据模型（纯数据，无行为）
 *
 * 承载从用户输入 + 设备模板解析出的所有信息，供各 SMV 模块构建器消费。
 * 由 DeviceSmvDataFactory 构建并填充所有字段。
 */
@Data
public class DeviceSmvData {

    // ── 设备标识 ──
    private String templateName;   // 模板名称（如 "Light"）

    // ── NuSMV 标识符（由 Factory 计算填充） ──
    private String moduleName;    // MODULE 名称（如 "Light_light1"）
    private String varName;       // 实例变量名（如 "light_1"），同时作为 deviceSmvMap 的 key
    private boolean sensor;       // 是否为传感器（无 API）

    // ── 模式与状态（从模板 Modes + WorkingStates 解析） ──
    private List<String> modes = new ArrayList<>();
    private Map<String, List<String>> modeStates = new LinkedHashMap<>();
    private List<String> states = new ArrayList<>();

    // ── 变量（从模板 InternalVariables 解析） ──
    private List<DeviceManifest.InternalVariable> variables = new ArrayList<>();
    private Map<String, DeviceManifest.InternalVariable> envVariables = new HashMap<>();
    private List<String> impactedVariables = new ArrayList<>();

    // ── 信号变量（从模板 Transitions[signal=true] + APIs[signal=true] 解析） ──
    private List<SignalInfo> signalVars = new ArrayList<>();

    // ── 内容（从模板 Contents 解析，如 Mobile Phone 的 photo） ──
    private List<ContentInfo> contents = new ArrayList<>();

    // ── 用户运行时输入 ──
    private String currentState;
    private Map<String, String> currentModeStates = new LinkedHashMap<>();
    private Map<String, String> variableValues = new HashMap<>();

    // ── 模板默认初始状态（从 manifest.InitState 解析） ──
    private Map<String, String> templateInitModeStates = new LinkedHashMap<>();

    // ── 信任/隐私（模板默认 + 用户实例覆盖） ──
    private Map<String, String> modeStateTrust = new LinkedHashMap<>();
    private String instanceStateTrust;
    private Map<String, String> instanceVariableTrust = new HashMap<>();
    private Map<String, String> instanceVariablePrivacy = new HashMap<>();

    // ── 模板引用 ──
    private transient DeviceManifest manifest;

    // ── 内部数据类 ──

    @Data
    public static class SignalInfo {
        private String name;
        private String start;
        private String end;
        private String trigger;
        private String type;
    }

    @Data
    public static class ContentInfo {
        private String name;       // content 名称（如 "photo"）
        private String privacy;    // 初始隐私（如 "private"）
        private boolean changeable; // IsChangeable → FROZENVAR(false) / VAR(true)
    }
}
