package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import com.fasterxml.jackson.core.type.TypeReference;
import org.springframework.stereotype.Component;

@Component
public class DeviceTemplateMapper {

    public DeviceTemplateDto toDto(DeviceTemplatePo po) {
        if (po == null) {
            return null;
        }
        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setId(po.getId());
        dto.setName(po.getName());

        DeviceManifest manifest = JsonUtils.fromJsonOrDefault(
                po.getManifestJson(),
                new TypeReference<DeviceManifest>() {},
                new DeviceManifest()
        );
        manifest.setName(dto.getName());
        dto.setManifest(manifest);
        return dto;
    }

    public DeviceTemplatePo toEntity(DeviceTemplateDto dto, Long userId) {
        if (dto == null) {
            return null;
        }
        return DeviceTemplatePo.builder()
                .userId(userId)
                .name(dto.getName())
                .manifestJson(JsonUtils.toJson(dto.getManifest()))
                .build();
    }
}
