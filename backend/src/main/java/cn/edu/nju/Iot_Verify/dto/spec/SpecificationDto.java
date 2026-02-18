// src/main/java/cn/edu/nju/Iot_Verify/dto/spec/SpecificationDto.java
package cn.edu.nju.Iot_Verify.dto.spec;

import com.fasterxml.jackson.annotation.JsonProperty;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.List;

@Data
@NoArgsConstructor
@AllArgsConstructor
public class SpecificationDto {

    @NotBlank(message = "Specification ID is required")
    private String id;

    @NotBlank(message = "Template ID is required")
    private String templateId;

    @NotBlank(message = "Template label is required")
    private String templateLabel;

    @NotNull(message = "A-conditions cannot be null")
    @JsonProperty("aConditions")
    private List<SpecConditionDto> aConditions = new ArrayList<>();

    @NotNull(message = "If-conditions cannot be null")
    private List<SpecConditionDto> ifConditions = new ArrayList<>();

    @NotNull(message = "Then-conditions cannot be null")
    private List<SpecConditionDto> thenConditions = new ArrayList<>();
}
