package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
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
        po.setConditionsJson("[{\"deviceName\":\"sensor\",\"attribute\":\"motion\","
                + "\"targetType\":\"variable\",\"relation\":\"=\",\"value\":\"active\"}]");
        po.setCommandJson("{\"deviceName\":\"light\",\"action\":\"turn_on\"}");
        po.setCreatedAt(now);

        RuleDto dto = mapper.toDto(po);

        assertEquals(now, dto.getCreatedAt());
    }

    @Test
    void toDto_blankOrSemanticallyEmptyRuleJsonFailsClosed() {
        RulePo blank = new RulePo();
        blank.setId(2L);
        blank.setConditionsJson("   ");
        blank.setCommandJson("{\"deviceName\":\"light\",\"action\":\"turn_on\"}");
        assertEquals("conditionsJson", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(blank)).getField());

        RulePo empty = new RulePo();
        empty.setId(3L);
        empty.setConditionsJson("[]");
        empty.setCommandJson("{}");
        assertEquals("conditionsJson", assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(empty)).getField());
    }

    @Test
    void toDto_unknownPersistedConditionFieldFailsClosed() {
        RulePo po = new RulePo();
        po.setId(4L);
        po.setConditionsJson("[{\"deviceName\":\"sensor\",\"attribute\":\"motion\","
                + "\"targetType\":\"variable\",\"relation\":\"=\",\"value\":\"active\","
                + "\"conditionIndex\":0}]");
        po.setCommandJson("{\"deviceName\":\"light\",\"action\":\"turn_on\"}");

        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));
        assertEquals("conditionsJson", error.getField());
    }
}
