// src/main/java/cn/edu/nju/Iot_Verify/util/DeviceEdgeMapper.java
package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.DeviceEdgeDto;
import cn.edu.nju.Iot_Verify.po.DeviceEdgePo;

public class DeviceEdgeMapper {

    public static DeviceEdgeDto toDto(DeviceEdgePo po) {
        DeviceEdgeDto dto = new DeviceEdgeDto();
        dto.setId(po.getId());
        dto.setFrom(po.getFrom());
        dto.setTo(po.getTo());
        dto.setFromLabel(po.getFromLabel());
        dto.setToLabel(po.getToLabel());
        dto.setFromApi(po.getFromApi());
        dto.setToApi(po.getToApi());

        DeviceEdgeDto.Point fp = new DeviceEdgeDto.Point();
        fp.setX(po.getFromPosX());
        fp.setY(po.getFromPosY());
        dto.setFromPos(fp);

        DeviceEdgeDto.Point tp = new DeviceEdgeDto.Point();
        tp.setX(po.getToPosX());
        tp.setY(po.getToPosY());
        dto.setToPos(tp);
        return dto;
    }

    public static DeviceEdgePo toPo(DeviceEdgeDto dto) {
        DeviceEdgeDto.Point fp = dto.getFromPos();
        DeviceEdgeDto.Point tp = dto.getToPos();
        return DeviceEdgePo.builder()
                .id(dto.getId())
                .from(dto.getFrom())
                .to(dto.getTo())
                .fromLabel(dto.getFromLabel())
                .toLabel(dto.getToLabel())
                .fromApi(dto.getFromApi())
                .toApi(dto.getToApi())
                .fromPosX(fp != null ? fp.getX() : 0.0)
                .fromPosY(fp != null ? fp.getY() : 0.0)
                .toPosX(tp != null ? tp.getX() : 0.0)
                .toPosY(tp != null ? tp.getY() : 0.0)
                .build();
    }
}
