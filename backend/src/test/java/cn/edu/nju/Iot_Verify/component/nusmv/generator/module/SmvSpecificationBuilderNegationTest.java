package cn.edu.nju.Iot_Verify.component.nusmv.generator.module;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for SmvSpecificationBuilder spec negation (Salus §5).
 */
class SmvSpecificationBuilderNegationTest {

    private final SmvSpecificationBuilder builder = new SmvSpecificationBuilder();

    private SpecificationDto buildSpec(String templateId,
                                        List<SpecConditionDto> aConditions,
                                        List<SpecConditionDto> ifConditions,
                                        List<SpecConditionDto> thenConditions) {
        SpecificationDto spec = new SpecificationDto();
        spec.setId("test-spec");
        spec.setTemplateId(templateId);
        spec.setAConditions(aConditions);
        spec.setIfConditions(ifConditions);
        spec.setThenConditions(thenConditions);
        return spec;
    }

    private SpecConditionDto buildCondition(String deviceId, String targetType, String key,
                                             String relation, String value) {
        SpecConditionDto cond = new SpecConditionDto();
        cond.setDeviceId(deviceId);
        cond.setTargetType(targetType);
        cond.setKey(key);
        cond.setRelation(relation);
        cond.setValue(value);
        return cond;
    }

    private Map<String, DeviceSmvData> buildDeviceMap() {
        // Minimal device with a state for condition resolution
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName("sensor_1");
        smv.setModuleName("SensorModule");
        smv.setModes(List.of("SensorState"));
        smv.setModeStates(Map.of("SensorState", List.of("active", "idle")));
        return Map.of("sensor_1", smv);
    }

    // ===== Template 1: always AG(A) → EF(!A) =====

    @Test
    void negate_template1_always() {
        SpecConditionDto cond = buildCondition("sensor_1", "state", null, "=", "active");
        SpecificationDto spec = buildSpec("1", List.of(cond), null, null);

        String negated = builder.generateNegatedSpec(spec, false, 0, buildDeviceMap());

        assertTrue(negated.startsWith("CTLSPEC EF(!("));
        assertTrue(negated.contains("sensor_1.SensorState=active"));
    }

    // ===== Template 1': always-imply AG(IF→THEN) → EF(IF & !THEN) =====

    @Test
    void negate_template1_alwaysImply() {
        SpecConditionDto ifCond = buildCondition("sensor_1", "state", null, "=", "active");
        SpecConditionDto thenCond = buildCondition("sensor_1", "state", null, "=", "idle");
        SpecificationDto spec = buildSpec("1", null, List.of(ifCond), List.of(thenCond));

        String negated = builder.generateNegatedSpec(spec, false, 0, buildDeviceMap());

        assertTrue(negated.startsWith("CTLSPEC EF("));
        assertTrue(negated.contains("& !("));
    }

    // ===== Template 2: eventually AF(A) → EG(!A) =====

    @Test
    void negate_template2_eventually() {
        SpecConditionDto cond = buildCondition("sensor_1", "state", null, "=", "active");
        SpecificationDto spec = buildSpec("2", List.of(cond), null, null);

        String negated = builder.generateNegatedSpec(spec, false, 0, buildDeviceMap());

        assertTrue(negated.startsWith("CTLSPEC EG(!("));
    }

    // ===== Template 3: never AG(!A) → EF(A) =====

    @Test
    void negate_template3_never() {
        SpecConditionDto cond = buildCondition("sensor_1", "state", null, "=", "active");
        SpecificationDto spec = buildSpec("3", List.of(cond), null, null);

        String negated = builder.generateNegatedSpec(spec, false, 0, buildDeviceMap());

        assertTrue(negated.startsWith("CTLSPEC EF("));
        assertFalse(negated.contains("!(")); // Not negated — EF(A) not EF(!A)
    }

    // ===== Template 4: immediate AG(IF→AX(THEN)) → EF(IF & EX(!THEN)) =====

    @Test
    void negate_template4_immediate() {
        SpecConditionDto ifCond = buildCondition("sensor_1", "state", null, "=", "active");
        SpecConditionDto thenCond = buildCondition("sensor_1", "state", null, "=", "idle");
        SpecificationDto spec = buildSpec("4", null, List.of(ifCond), List.of(thenCond));

        String negated = builder.generateNegatedSpec(spec, false, 0, buildDeviceMap());

        assertTrue(negated.startsWith("CTLSPEC EF("));
        assertTrue(negated.contains("EX(!("));
    }

    // ===== Template 5: response AG(IF→AF(THEN)) → EF(IF & EG(!THEN)) =====

    @Test
    void negate_template5_response() {
        SpecConditionDto ifCond = buildCondition("sensor_1", "state", null, "=", "active");
        SpecConditionDto thenCond = buildCondition("sensor_1", "state", null, "=", "idle");
        SpecificationDto spec = buildSpec("5", null, List.of(ifCond), List.of(thenCond));

        String negated = builder.generateNegatedSpec(spec, false, 0, buildDeviceMap());

        assertTrue(negated.startsWith("CTLSPEC EF("));
        assertTrue(negated.contains("EG(!("));
    }

    // ===== Template 6: persistence G(IF→FG(THEN)) → F(IF & GF(!THEN)) =====

    @Test
    void negate_template6_persistence() {
        SpecConditionDto ifCond = buildCondition("sensor_1", "state", null, "=", "active");
        SpecConditionDto thenCond = buildCondition("sensor_1", "state", null, "=", "idle");
        SpecificationDto spec = buildSpec("6", null, List.of(ifCond), List.of(thenCond));

        String negated = builder.generateNegatedSpec(spec, false, 0, buildDeviceMap());

        assertTrue(negated.startsWith("LTLSPEC F("));
        assertTrue(negated.contains("G F(!("));
    }

    // ===== Template 7: safety AG !(body) → EF(body) =====

    @Test
    void negate_template7_safety_noAttack() {
        SpecConditionDto cond = buildCondition("sensor_1", "state", null, "=", "active");
        SpecificationDto spec = buildSpec("7", List.of(cond), null, null);

        String negated = builder.generateNegatedSpec(spec, false, 0, buildDeviceMap());

        assertTrue(negated.startsWith("CTLSPEC EF("));
        assertTrue(negated.contains("sensor_1.SensorState=active"));
        // Should NOT contain negation — EF(body), not EF(!body)
        assertFalse(negated.contains("!("));
    }

    @Test
    void negate_template7_safety_withAttack() {
        SpecConditionDto cond = buildCondition("sensor_1", "state", null, "=", "active");
        SpecificationDto spec = buildSpec("7", List.of(cond), null, null);

        String negated = builder.generateNegatedSpec(spec, true, 3, buildDeviceMap());

        assertTrue(negated.startsWith("CTLSPEC EF("));
        assertTrue(negated.contains("sensor_1.SensorState=active"));
    }

    // ===== buildNegated integration =====

    @Test
    void buildNegated_emitsOnlyNegatedSpec() {
        SpecConditionDto cond = buildCondition("sensor_1", "state", null, "=", "active");
        SpecificationDto spec1 = buildSpec("1", List.of(cond), null, null);
        SpecificationDto spec2 = buildSpec("3", List.of(cond), null, null);

        String result = builder.buildNegated(List.of(spec1, spec2), 0,
                false, 0, buildDeviceMap(), false);

        assertTrue(result.contains("Negated specification (index 0)"));
        assertTrue(result.contains("CTLSPEC EF(!("));
        // Should NOT contain the second spec
        assertFalse(result.contains("AG !("));
    }

    @Test
    void buildNegated_invalidIndex_returnsEmpty() {
        assertEquals("", builder.buildNegated(List.of(), 0, false, 0, Map.of(), false));
        assertEquals("", builder.buildNegated(null, 0, false, 0, Map.of(), false));
    }
}
