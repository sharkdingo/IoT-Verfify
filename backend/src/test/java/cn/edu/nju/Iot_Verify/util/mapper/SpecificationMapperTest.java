package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.po.SpecificationPo;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class SpecificationMapperTest {

    private final SpecificationMapper mapper = new SpecificationMapper();

    @Test
    void toEntity_derivesConditionSideFromContainingCollection() {
        SpecificationDto spec = validSpec();
        spec.setAConditions(List.of(validCondition(null)));
        spec.setIfConditions(List.of(validCondition("then")));
        spec.setThenConditions(List.of(validCondition("if")));

        SpecificationPo po = mapper.toEntity(spec, 1L);

        assertEquals("a", readFirstSide(po.getAConditionsJson()));
        assertEquals("if", readFirstSide(po.getIfConditionsJson()));
        assertEquals("then", readFirstSide(po.getThenConditionsJson()));
    }

    @Test
    void toDto_normalizesLegacyPersistedConditionSides() {
        SpecificationPo po = new SpecificationPo();
        po.setId("spec_1");
        po.setUserId(1L);
        po.setTemplateId("1");
        po.setTemplateLabel("Always");
        po.setAConditionsJson(JsonUtils.toJsonOrEmpty(List.of(validCondition("then"))));
        po.setIfConditionsJson(JsonUtils.toJsonOrEmpty(List.of(validCondition(null))));
        po.setThenConditionsJson(JsonUtils.toJsonOrEmpty(List.of(validCondition("if"))));
        po.setDevicesJson("[]");

        SpecificationDto dto = mapper.toDto(po);

        assertEquals("a", dto.getAConditions().get(0).getSide());
        assertEquals("if", dto.getIfConditions().get(0).getSide());
        assertEquals("then", dto.getThenConditions().get(0).getSide());
    }

    @Test
    void statePropertyScope_roundTripsWithoutGeneratedStateKey() {
        SpecificationDto spec = validSpec();
        SpecConditionDto condition = validCondition("a");
        condition.setTargetType("privacy");
        condition.setPropertyScope("state");
        condition.setKey("SwitchState");
        condition.setValue("private");
        spec.setAConditions(List.of(condition));

        SpecificationPo po = mapper.toEntity(spec, 1L);
        SpecificationDto restored = mapper.toDto(po);

        SpecConditionDto restoredCondition = restored.getAConditions().get(0);
        assertEquals("state", restoredCondition.getPropertyScope());
        assertEquals("SwitchState", restoredCondition.getKey());
    }

    @Test
    void blankPersistedConditionColumnFailsClosedInsteadOfBecomingEmpty() {
        SpecificationPo po = new SpecificationPo();
        po.setId("spec_bad");
        po.setAConditionsJson(" ");
        po.setIfConditionsJson("[]");
        po.setThenConditionsJson("[]");
        po.setDevicesJson("[]");

        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));

        assertEquals("aConditionsJson", error.getField());
    }

    private SpecificationDto validSpec() {
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_1");
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        return spec;
    }

    private SpecConditionDto validCondition(String side) {
        SpecConditionDto condition = new SpecConditionDto();
        condition.setId("cond_1");
        condition.setSide(side);
        condition.setDeviceId("light");
        condition.setTargetType("state");
        condition.setKey("state");
        condition.setRelation("=");
        condition.setValue("on");
        return condition;
    }

    private String readFirstSide(String json) {
        return JsonUtils.fromJsonList(json, SpecConditionDto.class).get(0).getSide();
    }
}
