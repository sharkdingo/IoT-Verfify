package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.po.SpecificationPo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import org.springframework.stereotype.Component;

/**
 * Specification PO 与 DTO 之间的转换映射器
 */
@Component
public class SpecificationMapper {

    /**
     * SpecificationPo -> SpecificationDto
     */
    public SpecificationDto toDto(SpecificationPo po) {
        if (po == null) {
            return null;
        }
        SpecificationDto dto = new SpecificationDto();
        dto.setId(po.getId());
        dto.setTemplateId(po.getTemplateId());
        dto.setTemplateLabel(po.getTemplateLabel());

        dto.setAConditions(JsonUtils.fromJsonList(po.getAConditionsJson(), SpecConditionDto.class));
        dto.setIfConditions(JsonUtils.fromJsonList(po.getIfConditionsJson(), SpecConditionDto.class));
        dto.setThenConditions(JsonUtils.fromJsonList(po.getThenConditionsJson(), SpecConditionDto.class));

        return dto;
    }

    /**
     * SpecificationDto -> SpecificationPo
     */
    public SpecificationPo toEntity(SpecificationDto dto, Long userId) {
        if (dto == null) {
            return null;
        }
        SpecificationPo po = new SpecificationPo();
        po.setId(dto.getId());
        po.setUserId(userId);
        po.setTemplateId(dto.getTemplateId());
        po.setTemplateLabel(dto.getTemplateLabel());

        po.setAConditionsJson(JsonUtils.toJsonOrEmpty(dto.getAConditions()));
        po.setIfConditionsJson(JsonUtils.toJsonOrEmpty(dto.getIfConditions()));
        po.setThenConditionsJson(JsonUtils.toJsonOrEmpty(dto.getThenConditions()));

        return po;
    }

    public SpecificationPo toPo(SpecificationDto dto, Long userId) {
        return toEntity(dto, userId);
    }

    public String toJson(SpecificationDto dto) {
        return JsonUtils.toJson(dto);
    }
}
