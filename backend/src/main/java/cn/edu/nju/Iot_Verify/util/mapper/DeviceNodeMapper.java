package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import com.fasterxml.jackson.core.type.TypeReference;
import org.springframework.stereotype.Component;

import java.util.List;

/**
 * DeviceNode PO 与 DTO 之间的转换映射器
 */
@Component
public class DeviceNodeMapper {

    /**
     * DeviceNodePo -> DeviceNodeDto
     */
    public DeviceNodeDto toDto(DeviceNodePo po) {
        if (po == null) {
            return null;
        }
        DeviceNodeDto dto = new DeviceNodeDto();
        dto.setId(po.getId());
        dto.setTemplateName(po.getTemplateName());
        dto.setLabel(po.getLabel());

        DeviceNodeDto.Position pos = new DeviceNodeDto.Position();
        pos.setX(po.getPosX());
        pos.setY(po.getPosY());
        dto.setPosition(pos);

        dto.setState(po.getState());
        dto.setWidth(po.getWidth());
        dto.setHeight(po.getHeight());
        dto.setCurrentStateTrust(po.getCurrentStateTrust());

        if (po.getVariablesJson() != null && !po.getVariablesJson().isEmpty()) {
            dto.setVariables(JsonUtils.fromJsonOrDefault(
                    po.getVariablesJson(),
                    new TypeReference<List<VariableStateDto>>() {},
                    null
            ));
        }

        if (po.getPrivaciesJson() != null && !po.getPrivaciesJson().isEmpty()) {
            dto.setPrivacies(JsonUtils.fromJsonOrDefault(
                    po.getPrivaciesJson(),
                    new TypeReference<List<PrivacyStateDto>>() {},
                    null
            ));
        }

        return dto;
    }

    /**
     * DeviceNodeDto -> DeviceNodePo
     */
    public DeviceNodePo toEntity(DeviceNodeDto dto) {
        if (dto == null) {
            return null;
        }
        DeviceNodePo po = new DeviceNodePo();
        po.setId(dto.getId());
        po.setTemplateName(dto.getTemplateName());
        po.setLabel(dto.getLabel());

        if (dto.getPosition() != null) {
            po.setPosX(dto.getPosition().getX());
            po.setPosY(dto.getPosition().getY());
        }

        po.setState(dto.getState());
        po.setWidth(dto.getWidth());
        po.setHeight(dto.getHeight());
        po.setCurrentStateTrust(dto.getCurrentStateTrust());

        po.setVariablesJson(JsonUtils.toJsonOrEmpty(dto.getVariables()));
        po.setPrivaciesJson(JsonUtils.toJsonOrEmpty(dto.getPrivacies()));

        return po;
    }

    /**
     * DeviceNodeDto -> DeviceNodePo (with userId)
     */
    public DeviceNodePo toEntity(DeviceNodeDto dto, Long userId) {
        DeviceNodePo po = toEntity(dto);
        if (po != null) {
            po.setUserId(userId);
        }
        return po;
    }

    /**
     * DeviceNodeDto -> DeviceVerificationDto
     */
    public DeviceVerificationDto toVerificationDto(DeviceNodeDto dto) {
        if (dto == null) {
            return null;
        }
        DeviceVerificationDto vDto = new DeviceVerificationDto();
        vDto.setVarName(dto.getId());
        vDto.setTemplateName(dto.getTemplateName());
        vDto.setState(dto.getState());
        vDto.setCurrentStateTrust(dto.getCurrentStateTrust());
        vDto.setVariables(dto.getVariables());
        vDto.setPrivacies(dto.getPrivacies());
        return vDto;
    }
}
