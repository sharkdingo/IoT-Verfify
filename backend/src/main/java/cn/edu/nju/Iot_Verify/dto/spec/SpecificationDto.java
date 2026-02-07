// src/main/java/cn/edu/nju/Iot_Verify/dto/spec/SpecificationDto.java
package cn.edu.nju.Iot_Verify.dto.spec;

import com.fasterxml.jackson.annotation.JsonProperty;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.List;

@Data
@NoArgsConstructor
@AllArgsConstructor
public class SpecificationDto {

    private String id;
    private String templateId;
    private String templateLabel;

    @JsonProperty("aConditions")
    private List<SpecConditionDto> aConditions = new ArrayList<>();

    private List<SpecConditionDto> ifConditions = new ArrayList<>();
    private List<SpecConditionDto> thenConditions = new ArrayList<>();
}
