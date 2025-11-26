// src/main/java/cn/edu/nju/Iot_Verify/util/SpecificationMapper.java
package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.SpecificationDto;
import cn.edu.nju.Iot_Verify.po.SpecificationPo;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;

import java.util.Collections;
import java.util.List;

public class SpecificationMapper {

    private static final ObjectMapper OBJECT_MAPPER = new ObjectMapper();

    public static SpecificationDto toDto(SpecificationPo po) {
        SpecificationDto dto = new SpecificationDto();
        dto.setId(po.getId());
        dto.setTemplateId(po.getTemplateId());
        dto.setTemplateLabel(po.getTemplateLabel());
        dto.setAConditions(readList(po.getAConditionsJson()));
        dto.setIfConditions(readList(po.getIfConditionsJson()));
        dto.setThenConditions(readList(po.getThenConditionsJson()));
        return dto;
    }

    public static SpecificationPo toPo(SpecificationDto dto) {
        return SpecificationPo.builder()
                .id(dto.getId())
                .templateId(dto.getTemplateId())
                .templateLabel(dto.getTemplateLabel())
                .aConditionsJson(writeList(dto.getAConditions()))
                .ifConditionsJson(writeList(dto.getIfConditions()))
                .thenConditionsJson(writeList(dto.getThenConditions()))
                .build();
    }

    private static List<SpecConditionDto> readList(String json) {
        if (json == null || json.isBlank()) return Collections.emptyList();
        try {
            return OBJECT_MAPPER.readValue(
                    json,
                    new TypeReference<List<SpecConditionDto>>() {}
            );
        } catch (Exception e) {
            // 生产项目里建议好好处理，这里简单兜底
            return Collections.emptyList();
        }
    }

    private static String writeList(List<SpecConditionDto> list) {
        try {
            return OBJECT_MAPPER.writeValueAsString(list == null ? List.of() : list);
        } catch (Exception e) {
            return "[]";
        }
    }
}
