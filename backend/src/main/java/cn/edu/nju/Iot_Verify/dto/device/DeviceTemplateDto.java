package cn.edu.nju.Iot_Verify.dto.device;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

@Data
public class DeviceTemplateDto {

    private String id;

    @NotBlank(message = "Template name is required")
    private String name;

    @Valid
    private DeviceManifest manifest;

    /**
     * 设备模板 Manifest 的强类型定义
     */
    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    @JsonIgnoreProperties(ignoreUnknown = true)
    @JsonInclude(JsonInclude.Include.NON_NULL)
    public static class DeviceManifest {

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
        private List<Transition> transitions;

        @JsonProperty("APIs")
        private List<API> apis;

        @JsonProperty("Contents")
        private List<Content> contents;

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

            @JsonProperty("LowerBound")
            private Integer lowerBound;

            @JsonProperty("UpperBound")
            private Integer upperBound;

            @JsonProperty("NaturalChangeRate")
            private String naturalChangeRate;

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

            @JsonProperty("Value")
            private String value;

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
            private Trigger trigger;

            @JsonProperty("Assignments")
            private List<Assignment> assignments;
        }

        @Data
        @Builder
        @NoArgsConstructor
        @AllArgsConstructor
        @JsonIgnoreProperties(ignoreUnknown = true)
        public static class Transition {
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
            private Trigger trigger;

            @JsonProperty("Assignments")
            private List<Assignment> assignments;
        }

        @Data
        @Builder
        @NoArgsConstructor
        @AllArgsConstructor
        @JsonIgnoreProperties(ignoreUnknown = true)
        public static class Trigger {
            @JsonProperty("Attribute")
            private String attribute;

            @JsonProperty("Relation")
            private String relation;

            @JsonProperty("Value")
            private String value;
        }

        @Data
        @Builder
        @NoArgsConstructor
        @AllArgsConstructor
        @JsonIgnoreProperties(ignoreUnknown = true)
        public static class Assignment {
            @JsonProperty("Attribute")
            private String attribute;

            @JsonProperty("Value")
            private String value;
        }

        @Data
        @Builder
        @NoArgsConstructor
        @AllArgsConstructor
        @JsonIgnoreProperties(ignoreUnknown = true)
        public static class Content {
            @JsonProperty("Name")
            private String name;

            @JsonProperty("Privacy")
            private String privacy;

            @JsonProperty("IsChangeable")
            private Boolean isChangeable;
        }
    }
}
