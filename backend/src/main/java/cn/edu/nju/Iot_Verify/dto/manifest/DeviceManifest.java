package cn.edu.nju.Iot_Verify.dto.manifest;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * 设备模板 Manifest 的强类型定义
 * 对应前端新的 JSON 结构
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonIgnoreProperties(ignoreUnknown = true) // 忽略未知的字段，增强兼容性
@JsonInclude(JsonInclude.Include.NON_NULL)  // 不序列化 null 字段，保持 JSON 简洁
public class DeviceManifest {

    @JsonProperty("Name")
    private String name;

    @JsonProperty("Description")
    private String description;

    @JsonProperty("Modes")
    private List<String> modes;

    @JsonProperty("InternalVariables")
    private List<InternalVariable> internalVariables;

    @JsonProperty("ImpactedVariables")
    private List<String> impactedVariables;

    @JsonProperty("InitState")
    private String initState;

    @JsonProperty("WorkingStates")
    private List<WorkingState> workingStates;

    @JsonProperty("Transitions")
    private List<Object> transitions;

    @JsonProperty("APIs")
    private List<API> apis;

    // ================= 内部类 =================

    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    @JsonIgnoreProperties(ignoreUnknown = true)
    public static class InternalVariable {
        @JsonProperty("Name")
        private String name;

        @JsonProperty("Description")
        private String description;

        @JsonProperty("IsInside")
        private Boolean isInside;

        @JsonProperty("PublicVisible")
        private Boolean publicVisible;

        @JsonProperty("Trust")
        private String trust;

        @JsonProperty("Privacy")
        private String privacy;

        // 数值型属性
        @JsonProperty("LowerBound")
        private Double lowerBound;

        @JsonProperty("UpperBound")
        private Double upperBound;

        @JsonProperty("NaturalChangeRate")
        private String naturalChangeRate;

        // 枚举型属性
        @JsonProperty("Values")
        private List<String> values;
    }

    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    @JsonIgnoreProperties(ignoreUnknown = true)
    public static class WorkingState {
        @JsonProperty("Name")
        private String name;

        @JsonProperty("Description")
        private String description;

        @JsonProperty("Trust")
        private String trust;

        @JsonProperty("Privacy")
        private String privacy;

        @JsonProperty("Invariant")
        private String invariant;

        @JsonProperty("Dynamics")
        private List<Dynamic> dynamics;
    }

    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    @JsonIgnoreProperties(ignoreUnknown = true)
    public static class Dynamic {
        @JsonProperty("VariableName")
        private String variableName;

        @JsonProperty("ChangeRate")
        private String changeRate;
    }

    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    @JsonIgnoreProperties(ignoreUnknown = true)
    public static class API {
        @JsonProperty("Name")
        private String name;

        @JsonProperty("Description")
        private String description;

        @JsonProperty("Signal")
        private Boolean signal;

        @JsonProperty("StartState")
        private String startState;

        @JsonProperty("EndState")
        private String endState;

        @JsonProperty("Trigger")
        private String trigger;

        @JsonProperty("Assignments")
        private List<Object> assignments;
    }
}