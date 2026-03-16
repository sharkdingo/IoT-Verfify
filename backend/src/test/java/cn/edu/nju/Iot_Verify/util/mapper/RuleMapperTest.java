package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.po.RulePo;
import org.junit.jupiter.api.Test;

import java.time.LocalDateTime;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class RuleMapperTest {

    private final RuleMapper mapper = new RuleMapper();

    @Test
    void toEntity_shouldIgnoreClientProvidedCreatedAt() {
        LocalDateTime forgedTime = LocalDateTime.of(2000, 1, 1, 0, 0);

        RuleDto dto = new RuleDto();
        dto.setConditions(List.of());
        dto.setCommand(new RuleDto.Command("dev", "on", null, null));
        dto.setRuleString("test rule");
        dto.setCreatedAt(forgedTime);

        RulePo po = mapper.toEntity(dto, 1L);

        assertNull(po.getCreatedAt(),
                "createdAt must be null so @PrePersist sets it; client value must be ignored");
    }

    @Test
    void toDto_shouldMapCreatedAtFromPo() {
        LocalDateTime now = LocalDateTime.now();

        RulePo po = new RulePo();
        po.setId(1L);
        po.setUserId(1L);
        po.setConditionsJson("[]");
        po.setCommandJson("{}");
        po.setCreatedAt(now);

        RuleDto dto = mapper.toDto(po);

        assertEquals(now, dto.getCreatedAt());
    }
}
