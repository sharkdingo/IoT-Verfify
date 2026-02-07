package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.rule.DeviceEdgeDto;
import cn.edu.nju.Iot_Verify.po.DeviceEdgePo;
import org.springframework.stereotype.Component;

/**
 * DeviceEdge PO 与 DTO 之间的转换映射器
 */
@Component
public class DeviceEdgeMapper {

    /**
     * DeviceEdgePo -> DeviceEdgeDto
     */
    public DeviceEdgeDto toDto(DeviceEdgePo po) {
        if (po == null) {
            return null;
        }
        DeviceEdgeDto dto = new DeviceEdgeDto();
        dto.setId(po.getId());
        dto.setFrom(po.getFrom());
        dto.setTo(po.getTo());
        dto.setFromLabel(po.getFromLabel());
        dto.setToLabel(po.getToLabel());
        dto.setFromApi(po.getFromApi());
        dto.setToApi(po.getToApi());

        DeviceEdgeDto.Point fromPos = new DeviceEdgeDto.Point();
        fromPos.setX(po.getFromPosX());
        fromPos.setY(po.getFromPosY());
        dto.setFromPos(fromPos);

        DeviceEdgeDto.Point toPos = new DeviceEdgeDto.Point();
        toPos.setX(po.getToPosX());
        toPos.setY(po.getToPosY());
        dto.setToPos(toPos);

        return dto;
    }

    /**
     * DeviceEdgeDto -> DeviceEdgePo
     */
    public DeviceEdgePo toEntity(DeviceEdgeDto dto) {
        if (dto == null) {
            return null;
        }
        DeviceEdgePo po = new DeviceEdgePo();
        po.setId(dto.getId());
        po.setFrom(dto.getFrom());
        po.setTo(dto.getTo());
        po.setFromLabel(dto.getFromLabel());
        po.setToLabel(dto.getToLabel());
        po.setFromApi(dto.getFromApi());
        po.setToApi(dto.getToApi());

        if (dto.getFromPos() != null) {
            po.setFromPosX(dto.getFromPos().getX());
            po.setFromPosY(dto.getFromPos().getY());
        }

        if (dto.getToPos() != null) {
            po.setToPosX(dto.getToPos().getX());
            po.setToPosY(dto.getToPos().getY());
        }

        return po;
    }

    /**
     * DeviceEdgeDto -> DeviceEdgePo (with userId)
     */
    public DeviceEdgePo toEntity(DeviceEdgeDto dto, Long userId) {
        DeviceEdgePo po = toEntity(dto);
        if (po != null) {
            po.setUserId(userId);
        }
        return po;
    }
}
