// src/main/java/cn/edu/nju/Iot_Verify/dto/spec/SpecificationDto.java
package cn.edu.nju.Iot_Verify.dto.spec;

import com.fasterxml.jackson.annotation.JsonProperty;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Size;
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
    @Size(max = 100, message = "Specification ID must be at most 100 characters")
    private String id;

    @NotBlank(message = "Template ID is required")
    @Size(max = 10, message = "Template ID must be at most 10 characters")
    private String templateId;

    @NotBlank(message = "Template label is required")
    @Size(max = 255, message = "Template label must be at most 255 characters")
    private String templateLabel;

    @Valid
    @NotNull(message = "A-conditions cannot be null")
    @JsonProperty("aConditions")
    private List<SpecConditionDto> aConditions = new ArrayList<>();

    @Valid
    @NotNull(message = "If-conditions cannot be null")
    private List<SpecConditionDto> ifConditions = new ArrayList<>();

    @Valid
    @NotNull(message = "Then-conditions cannot be null")
    private List<SpecConditionDto> thenConditions = new ArrayList<>();
}
