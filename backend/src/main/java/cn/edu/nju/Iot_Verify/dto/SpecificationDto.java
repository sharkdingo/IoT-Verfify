// src/main/java/cn/edu/nju/Iot_Verify/dto/SpecificationDto.java
package cn.edu.nju.Iot_Verify.dto;

import com.fasterxml.jackson.annotation.JsonIgnoreProperties;
import com.fasterxml.jackson.annotation.JsonProperty;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.ArrayList;
import java.util.List;

@Data
@NoArgsConstructor
@AllArgsConstructor
// 无论哪里还有叫 "aconditions" 的属性，序列化/反序列化都忽略掉
@JsonIgnoreProperties(value = {"aconditions"})
public class SpecificationDto {

    private String id;
    private String templateId;
    private String templateLabel;

    // 明确告诉 Jackson：这个字段在 JSON 中就叫 aConditions
    @JsonProperty("aConditions")
    private List<SpecConditionDto> aConditions = new ArrayList<>();

    private List<SpecConditionDto> ifConditions = new ArrayList<>();
    private List<SpecConditionDto> thenConditions = new ArrayList<>();
}
