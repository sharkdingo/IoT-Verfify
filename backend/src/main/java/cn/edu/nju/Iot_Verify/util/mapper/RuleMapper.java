package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.po.RulePo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import com.fasterxml.jackson.core.type.TypeReference;
import org.springframework.stereotype.Component;

import java.util.List;

/**
 * Rule PO 与 DTO 之间的转换映射器
 */
@Component
public class RuleMapper {

    /**
     * RulePo -> RuleDto
     */
    public RuleDto toDto(RulePo po) {
        if (po == null) {
            return null;
        }
        RuleDto dto = new RuleDto();
        dto.setId(po.getId());
        dto.setUserId(po.getUserId());
        dto.setRuleString(po.getRuleString());
        dto.setCreatedAt(po.getCreatedAt());

        List<RuleDto.Condition> conditions = JsonUtils.readPersistedJsonRequired(
                "rule", po.getId(), "conditionsJson", po.getConditionsJson(),
                () -> JsonUtils.fromJson(
                        po.getConditionsJson(), new TypeReference<List<RuleDto.Condition>>() {}));
        if (conditions.isEmpty()) {
            throw new PersistedDataIntegrityException(
                    "rule", po.getId(), "conditionsJson", "rule has no trigger conditions");
        }
        dto.setConditions(conditions);

        RuleDto.Command command = JsonUtils.readPersistedJsonRequired(
                "rule", po.getId(), "commandJson", po.getCommandJson(),
                () -> JsonUtils.fromJson(
                        po.getCommandJson(), new TypeReference<RuleDto.Command>() {}));
        if (command.getDeviceName() == null || command.getDeviceName().isBlank()
                || command.getAction() == null || command.getAction().isBlank()) {
            throw new PersistedDataIntegrityException(
                    "rule", po.getId(), "commandJson", "command device and action are required");
        }
        dto.setCommand(command);

        return dto;
    }

    /**
     * RuleDto -> RulePo
     */
    public RulePo toEntity(RuleDto dto, Long userId) {
        if (dto == null) {
            return null;
        }
        RulePo po = new RulePo();
        po.setId(dto.getId());
        po.setUserId(userId);
        po.setRuleString(dto.getRuleString());
        // createdAt is server-managed: @PrePersist sets it for new entities,
        // service layer restores it from DB for updates. Never trust client value.

        if (dto.getConditions() != null) {
            po.setConditionsJson(JsonUtils.toJson(dto.getConditions()));
        } else {
            po.setConditionsJson("[]");
        }

        if (dto.getCommand() != null) {
            po.setCommandJson(JsonUtils.toJson(dto.getCommand()));
        } else {
            po.setCommandJson("{}");
        }

        return po;
    }
}
