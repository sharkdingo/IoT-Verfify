// src/main/java/cn/edu/nju/Iot_Verify/dto/spec/SpecificationDto.java
package cn.edu.nju.Iot_Verify.dto.spec;

import com.fasterxml.jackson.annotation.JsonAutoDetect;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;
import jakarta.validation.Valid;
import jakarta.validation.constraints.AssertTrue;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Pattern;
import jakarta.validation.constraints.Size;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.List;

@Data
@NoArgsConstructor
@AllArgsConstructor
@JsonAutoDetect(getterVisibility = JsonAutoDetect.Visibility.NONE,
                isGetterVisibility = JsonAutoDetect.Visibility.NONE,
                fieldVisibility = JsonAutoDetect.Visibility.ANY)
public class SpecificationDto {

    @NotBlank(message = "Specification ID is required")
    @Size(max = 100, message = "Specification ID must be at most 100 characters")
    private String id;

    @NotBlank(message = "Template ID is required")
    @Pattern(regexp = "^[1-7]$", message = "Template ID must be one of 1, 2, 3, 4, 5, 6, 7")
    @Size(max = 10, message = "Template ID must be at most 10 characters")
    private String templateId;

    @NotBlank(message = "Template label is required")
    @Size(max = 255, message = "Template label must be at most 255 characters")
    private String templateLabel;

    @Valid
    @NotNull(message = "A-conditions cannot be null")
    @JsonProperty("aConditions")
    private List<@Valid @NotNull(message = "A-condition item cannot be null") SpecConditionDto> aConditions = new ArrayList<>();

    @Valid
    @NotNull(message = "If-conditions cannot be null")
    private List<@Valid @NotNull(message = "If-condition item cannot be null") SpecConditionDto> ifConditions = new ArrayList<>();

    @Valid
    @NotNull(message = "Then-conditions cannot be null")
    private List<@Valid @NotNull(message = "Then-condition item cannot be null") SpecConditionDto> thenConditions = new ArrayList<>();

    @Size(max = 4000, message = "Formula must be at most 4000 characters")
    private String formula;

    @Valid
    @NotNull(message = "Devices cannot be null")
    @Size(max = 50, message = "At most 50 devices can be bound to a specification")
    private List<@Valid @NotNull(message = "Specification device item cannot be null") DeviceRefDto> devices = new ArrayList<>();

    @Data
    @NoArgsConstructor
    @AllArgsConstructor
    public static class DeviceRefDto {
        @Size(max = 100, message = "Device ID must be at most 100 characters")
        private String deviceId;

        @Size(max = 100, message = "Device label must be at most 100 characters")
        private String deviceLabel;

        @NotNull(message = "Selected APIs cannot be null")
        @Size(max = 100, message = "At most 100 APIs can be selected for a specification device")
        private List<@NotNull(message = "Selected API name cannot be null")
                @Size(max = 100, message = "Selected API name must be at most 100 characters") String> selectedApis = new ArrayList<>();

        @JsonIgnore
        @AssertTrue(message = "Specification device must include deviceId or deviceLabel")
        public boolean isDeviceReferencePresent() {
            return hasText(deviceId) || hasText(deviceLabel);
        }

        private boolean hasText(String value) {
            return value != null && !value.isBlank();
        }
    }

    @JsonIgnore
    @AssertTrue(message = "Specification condition side must match its containing collection")
    public boolean isConditionSidesConsistent() {
        return conditionSidesMatch(aConditions, "a")
                && conditionSidesMatch(ifConditions, "if")
                && conditionSidesMatch(thenConditions, "then");
    }

    private boolean conditionSidesMatch(List<SpecConditionDto> conditions, String expectedSide) {
        if (conditions == null) {
            return true;
        }
        for (SpecConditionDto condition : conditions) {
            if (condition == null) {
                continue;
            }
            String side = condition.getSide();
            if (side != null && !side.isBlank() && !expectedSide.equals(side)) {
                return false;
            }
        }
        return true;
    }
}
