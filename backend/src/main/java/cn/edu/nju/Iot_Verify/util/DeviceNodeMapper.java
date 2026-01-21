package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.po.DeviceNodePo;

public class DeviceNodeMapper {

    public static DeviceNodeDto toDto(DeviceNodePo po) {
        DeviceNodeDto dto = new DeviceNodeDto();
        dto.setId(po.getId());
        dto.setTemplateName(po.getTemplateName());
        dto.setLabel(po.getLabel());
        dto.setState(po.getState());
        dto.setWidth(po.getWidth());
        dto.setHeight(po.getHeight());

        DeviceNodeDto.Position pos = new DeviceNodeDto.Position();
        pos.setX(po.getPosX());
        pos.setY(po.getPosY());
        dto.setPosition(pos);
        return dto;
    }

    public static DeviceNodePo toPo(DeviceNodeDto dto, Long userId) {
        return DeviceNodePo.builder()
                .id(dto.getId())
                .userId(userId)
                .templateName(dto.getTemplateName())
                .label(dto.getLabel())
                .state(dto.getState())
                .width(dto.getWidth())
                .height(dto.getHeight())
                .posX(dto.getPosition() != null ? dto.getPosition().getX() : 250.0)
                .posY(dto.getPosition() != null ? dto.getPosition().getY() : 250.0)
                .build();
    }
}
