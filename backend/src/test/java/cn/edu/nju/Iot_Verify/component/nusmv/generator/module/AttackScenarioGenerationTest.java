package cn.edu.nju.Iot_Verify.component.nusmv.generator.module;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.AttackActivation;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.model.AttackPointDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class AttackScenarioGenerationTest {

    @Test
    void deviceAttackInitializerIsFixedForExactScenario() {
        SmvDeviceModuleBuilder builder = new SmvDeviceModuleBuilder();
        DeviceSmvData device = new DeviceSmvData();
        device.setModuleName("Light_light_1");
        device.setVarName("light_1");
        device.setManifest(new DeviceManifest());

        String compromised = builder.build(device, AttackActivation.FIXED_COMPROMISED, false);
        String safe = builder.build(device, AttackActivation.FIXED_SAFE, false);
        String exhaustive = builder.build(device, AttackActivation.NONDETERMINISTIC, false);

        assertTrue(compromised.contains("init(is_attack) := TRUE;"));
        assertTrue(safe.contains("init(is_attack) := FALSE;"));
        assertTrue(exhaustive.contains("init(is_attack) := {TRUE, FALSE};"));
    }

    @Test
    void automationLinkInitializerUsesStablePersistedRuleId() throws Exception {
        Method initializer = SmvMainModuleBuilder.class.getDeclaredMethod(
                "automationLinkAttackInitializer", AttackScenarioDto.class, RuleDto.class);
        initializer.setAccessible(true);
        AttackScenarioDto exact = AttackScenarioDto.exactPoints(List.of(
                AttackPointDto.automationLink(7L)));

        assertEquals("TRUE", initializer.invoke(null, exact, RuleDto.builder().id(7L).build()));
        assertEquals("FALSE", initializer.invoke(null, exact, RuleDto.builder().id(8L).build()));
        assertEquals("{TRUE, FALSE}", initializer.invoke(null,
                AttackScenarioDto.anyUpToBudget(1), RuleDto.builder().id(8L).build()));
    }
}
