package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.po.DeviceNodePo;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import com.fasterxml.jackson.core.type.TypeReference;
import org.springframework.stereotype.Component;

import java.util.List;

/**
 * DeviceNode PO 与 DTO 之间的转换映射器
 */
@Component
public class DeviceNodeMapper {

    private static final String FALLBACK_STATE = "Working";

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

        String state = po.getState();
        if (state == null || state.isBlank()) {
            throw new PersistedDataIntegrityException("device", po.getId(), "state", "state is missing");
        }
        dto.setState(state);
        dto.setWidth(po.getWidth());
        dto.setHeight(po.getHeight());
        dto.setCurrentStateTrust(po.getCurrentStateTrust());
        dto.setCurrentStatePrivacy(po.getCurrentStatePrivacy());

        if (po.getVariablesJson() != null) {
            dto.setVariables(JsonUtils.readPersistedJsonOptional(
                    "device", po.getId(), "variablesJson", po.getVariablesJson(),
                    () -> JsonUtils.fromJson(
                            po.getVariablesJson(), new TypeReference<List<VariableStateDto>>() {})));
        }

        if (po.getPrivaciesJson() != null) {
            dto.setPrivacies(JsonUtils.readPersistedJsonOptional(
                    "device", po.getId(), "privaciesJson", po.getPrivaciesJson(),
                    () -> JsonUtils.fromJson(
                            po.getPrivaciesJson(), new TypeReference<List<PrivacyStateDto>>() {})));
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

        String state = dto.getState();
        po.setState(state != null && !state.isBlank() ? state.trim() : FALLBACK_STATE);
        po.setWidth(dto.getWidth());
        po.setHeight(dto.getHeight());
        po.setCurrentStateTrust(dto.getCurrentStateTrust());
        po.setCurrentStatePrivacy(dto.getCurrentStatePrivacy());

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

}
