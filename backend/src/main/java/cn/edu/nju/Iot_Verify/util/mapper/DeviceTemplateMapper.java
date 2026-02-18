package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import com.fasterxml.jackson.core.type.TypeReference;
import org.springframework.stereotype.Component;

import java.util.List;

/**
 * DeviceTemplate PO 与 DTO 之间的转换映射器
 */
@Component
public class DeviceTemplateMapper {

    /**
     * DeviceTemplatePo -> DeviceTemplateDto
     */
    public DeviceTemplateDto toDto(DeviceTemplatePo po) {
        if (po == null) {
            return null;
        }
        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setId(po.getId() != null ? po.getId().toString() : null);
        dto.setName(po.getName());

        if (po.getManifestJson() != null && !po.getManifestJson().isEmpty()) {
            DeviceTemplateDto.DeviceManifest manifest = JsonUtils.fromJsonOrDefault(
                    po.getManifestJson(),
                    new TypeReference<DeviceTemplateDto.DeviceManifest>() {},
                    null
            );
            dto.setManifest(manifest);
        }

        return dto;
    }

    /**
     * DeviceTemplateDto -> DeviceTemplatePo
     */
    public DeviceTemplatePo toEntity(DeviceTemplateDto dto) {
        if (dto == null) {
            return null;
        }
        DeviceTemplatePo po = new DeviceTemplatePo();
        po.setName(dto.getName());
        po.setManifestJson(JsonUtils.toJson(dto.getManifest()));
        return po;
    }

    /**
     * DeviceTemplateDto -> DeviceTemplatePo (with userId)
     */
    public DeviceTemplatePo toEntity(DeviceTemplateDto dto, Long userId) {
        DeviceTemplatePo po = toEntity(dto);
        if (po != null) {
            po.setUserId(userId);
        }
        return po;
    }

    /**
     * List<DeviceTemplatePo> -> List<DeviceTemplateDto>
     */
    public List<DeviceTemplateDto> toDtoList(List<DeviceTemplatePo> poList) {
        return poList.stream().map(this::toDto).toList();
    }
}
