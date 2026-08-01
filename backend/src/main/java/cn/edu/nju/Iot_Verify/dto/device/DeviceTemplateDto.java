package cn.edu.nju.Iot_Verify.dto.device;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;
import jakarta.validation.Valid;
import jakarta.validation.constraints.AssertTrue;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Pattern;
import jakarta.validation.constraints.Size;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

@Data
public class DeviceTemplateDto {

    private Long id;

    @NotBlank(message = "Template name is required")
    @Size(max = 100, message = "Template name must be at most 100 characters")
    private String name;

    @NotNull(message = "Template manifest is required")
    @Valid
    private DeviceManifest manifest;

    private Boolean defaultTemplate;

    /**
     * 设备模板 Manifest 的强类型定义
     */
    @Data
    @Builder
    @NoArgsConstructor
    @AllArgsConstructor
    @JsonInclude(JsonInclude.Include.NON_NULL)
    public static class DeviceManifest {
        @JsonProperty("Name")
        private String name;

        @JsonProperty("Description")
        private String description;

        @JsonProperty("Icon")
        private String icon;

        @JsonProperty("Modes")
        private List<String> modes;

        @JsonProperty("InternalVariables")
        @Valid
        private List<InternalVariable> internalVariables;


        @JsonProperty("ImpactedVariables")
        private List<String> impactedVariables;

        @JsonProperty("InitState")
        private String initState;

        @JsonProperty("WorkingStates")
        @Valid
        private List<WorkingState> workingStates;

        @JsonProperty("Transitions")
        private List<Transition> transitions;

        @JsonProperty("APIs")
        @Valid
        private List<API> apis;

        @JsonProperty("Contents")
        @Valid
        private List<Content> contents;

        @Data
        @Builder
        @NoArgsConstructor
        @AllArgsConstructor
        @JsonInclude(JsonInclude.Include.NON_NULL)
        public static class InternalVariable {
            @JsonProperty("Name")
            private String name;

            @JsonProperty("Description")
            private String description;

            @JsonProperty("IsInside")
            @NotNull(message = "InternalVariable IsInside must explicitly choose device-local or shared scope")
            private Boolean isInside;

            /** Whether compromise may replace this reported value with any value in its declared domain. */
            @JsonProperty("FalsifiableWhenCompromised")
            @NotNull(message = "InternalVariable FalsifiableWhenCompromised must explicitly define compromise behavior")
            private Boolean falsifiableWhenCompromised;

            /**
             * Whether this device reads the shared value, i.e. whether its rules and specifications may
             * use it as a condition source and whether it gets a {@code device.name := a_name} mirror.
             *
             * <p>Required on a shared declaration ({@code IsInside=false}) and rejected on a
             * device-local one, for the same reason {@code IsInside} and
             * {@code FalsifiableWhenCompromised} are required: a capability must never come from a
             * missing field. While read capability was implied by <em>which array</em> a declaration
             * lived in, omitting it silently granted access; a default would reintroduce exactly that.
             */
            @JsonProperty("Reads")
            private Boolean reads;

            @AssertTrue(message = "InternalVariable Reads must be explicit for a shared variable "
                    + "(IsInside=false) and omitted for a device-local one")
            private boolean isValidReadCapability() {
                if (isInside == null) return true; // reported by the IsInside NotNull constraint
                return isInside ? reads == null : reads != null;
            }

            @JsonProperty("Trust")
            @NotBlank(message = "InternalVariable Trust must be explicit")
            @Pattern(regexp = "trusted|untrusted", message = "InternalVariable Trust must be trusted or untrusted")
            private String trust;

            @JsonProperty("Privacy")
            @NotBlank(message = "InternalVariable Privacy must be explicit")
            @Pattern(regexp = "public|private", message = "InternalVariable Privacy must be public or private")
            private String privacy;

            @JsonProperty("LowerBound")
            private Integer lowerBound;

            @JsonProperty("UpperBound")
            private Integer upperBound;

            @JsonProperty("NaturalChangeRate")
            private String naturalChangeRate;

            @JsonProperty("Values")
            private List<String> values;

            @AssertTrue(message = "InternalVariable must explicitly define either Values OR LowerBound+UpperBound")
            private boolean isValidVariableDefinition() {
                boolean hasValues = values != null && !values.isEmpty();
                boolean hasLower = lowerBound != null;
                boolean hasUpper = upperBound != null;
                boolean hasAnyBound = hasLower || hasUpper;
                boolean hasFullRange = hasLower && hasUpper;
                return hasValues != hasFullRange && (!hasAnyBound || hasFullRange);
            }
        }

        @Data
        @Builder
        @NoArgsConstructor
        @AllArgsConstructor
        @JsonInclude(JsonInclude.Include.NON_NULL)
        public static class WorkingState {
            @JsonProperty("Name")
            private String name;

            @JsonProperty("Description")
            private String description;

            @JsonProperty("Trust")
            @NotBlank(message = "WorkingState Trust must be explicit")
            @Pattern(regexp = "trusted|untrusted", message = "WorkingState Trust must be trusted or untrusted")
            private String trust;

            @JsonProperty("Privacy")
            @NotBlank(message = "WorkingState Privacy must be explicit")
            @Pattern(regexp = "public|private", message = "WorkingState Privacy must be public or private")
            private String privacy;

            @JsonProperty("Dynamics")
            @Valid
            private List<Dynamic> dynamics;
        }

        @Data
        @Builder
        @NoArgsConstructor
        @AllArgsConstructor
        @JsonInclude(JsonInclude.Include.NON_NULL)
        public static class Dynamic {
            @JsonProperty("VariableName")
            private String variableName;

            @JsonProperty("Value")
            private String value;

            @JsonProperty("ChangeRate")
            private String changeRate;

            @AssertTrue(message = "Dynamic must have either ChangeRate OR Value, not both or neither")
            private boolean isValidDynamic() {
                boolean hasChangeRate = changeRate != null && !changeRate.isBlank();
                boolean hasValue = value != null && !value.isBlank();
                // XOR: exactly one must be true
                return hasChangeRate != hasValue;
            }
        }

        @Data
        @Builder
        @NoArgsConstructor
        @AllArgsConstructor
        @JsonInclude(JsonInclude.Include.NON_NULL)
        public static class API {
            @JsonProperty("Name")
            private String name;

            @JsonProperty("Description")
            private String description;

            @JsonProperty("Signal")
            @NotNull(message = "API Signal must explicitly choose whether the action is observable as a trigger")
            private Boolean signal;

            @JsonProperty("AcceptsContent")
            private Boolean acceptsContent;

            @JsonProperty("StartState")
            @NotNull(message = "API StartState must explicitly define a state precondition or an empty any-state value")
            private String startState;

            @JsonProperty("EndState")
            private String endState;

            @JsonProperty("Trigger")
            private Trigger trigger;

        }

        @Data
        @Builder
        @NoArgsConstructor
        @AllArgsConstructor
        @JsonInclude(JsonInclude.Include.NON_NULL)
        public static class Transition {
            @JsonProperty("Name")
            private String name;

            @JsonProperty("Description")
            private String description;

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
        @JsonInclude(JsonInclude.Include.NON_NULL)
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
        @JsonInclude(JsonInclude.Include.NON_NULL)
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
        @JsonInclude(JsonInclude.Include.NON_NULL)
        public static class Content {
            @JsonProperty("Name")
            private String name;

            @JsonProperty("Description")
            private String description;

            @JsonProperty("Privacy")
            @NotBlank(message = "Content Privacy must be explicit")
            @Pattern(regexp = "public|private", message = "Content Privacy must be public or private")
            private String privacy;
        }

        /**
         * Domain/defaults for a shared environment value this template can affect but
         * does not necessarily read. Unlike an external InternalVariable, this entry
         * grants no read capability and creates no device-module variable.
         */
    }
}
