package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
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

        if (po.getConditionsJson() != null && !po.getConditionsJson().isEmpty()) {
            dto.setConditions(JsonUtils.fromJsonOrDefault(
                    po.getConditionsJson(),
                    new TypeReference<List<RuleDto.Condition>>() {},
                    List.of()
            ));
        }

        if (po.getCommandJson() != null && !po.getCommandJson().isEmpty()) {
            dto.setCommand(JsonUtils.fromJsonOrDefault(
                    po.getCommandJson(),
                    new TypeReference<RuleDto.Command>() {},
                    null
            ));
        }

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
