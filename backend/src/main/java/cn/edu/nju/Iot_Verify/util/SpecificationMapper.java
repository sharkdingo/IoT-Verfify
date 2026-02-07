package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.po.SpecificationPo;
import com.fasterxml.jackson.core.type.TypeReference;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.Collections;
import java.util.List;

@Slf4j
@Component
@RequiredArgsConstructor
public class SpecificationMapper {

    private final ObjectMapper objectMapper;

    public SpecificationDto toDto(SpecificationPo po) {
        SpecificationDto dto = new SpecificationDto();
        dto.setId(po.getId());
        dto.setTemplateId(po.getTemplateId());
        dto.setTemplateLabel(po.getTemplateLabel());
        dto.setAConditions(readList(po.getAConditionsJson()));
        dto.setIfConditions(readList(po.getIfConditionsJson()));
        dto.setThenConditions(readList(po.getThenConditionsJson()));
        return dto;
    }

    public SpecificationPo toPo(SpecificationDto dto, Long userId) {
        return SpecificationPo.builder()
                .id(dto.getId())
                .userId(userId)
                .templateId(dto.getTemplateId())
                .templateLabel(dto.getTemplateLabel())
                .aConditionsJson(writeList(dto.getAConditions()))
                .ifConditionsJson(writeList(dto.getIfConditions()))
                .thenConditionsJson(writeList(dto.getThenConditions()))
                .build();
    }

    private List<SpecConditionDto> readList(String json) {
        if (json == null || json.isBlank()) return Collections.emptyList();
        try {
            return objectMapper.readValue(json, new TypeReference<List<SpecConditionDto>>() {});
        } catch (Exception e) {
            log.warn("Failed to parse conditions JSON: {}", json, e);
            return Collections.emptyList();
        }
    }

    private String writeList(List<SpecConditionDto> list) {
        try {
            return objectMapper.writeValueAsString(list == null ? List.of() : list);
        } catch (Exception e) {
            log.warn("Failed to serialize conditions", e);
            return "[]";
        }
    }

    /**
     * 将 SpecificationDto 转换为 JSON 字符串
     */
    public String toJson(SpecificationDto dto) {
        try {
            return objectMapper.writeValueAsString(dto);
        } catch (Exception e) {
            log.warn("Failed to serialize specification", e);
            return "{}";
        }
    }
}
