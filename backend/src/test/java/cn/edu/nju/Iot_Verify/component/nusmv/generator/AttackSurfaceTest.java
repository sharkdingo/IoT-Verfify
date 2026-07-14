package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

class AttackSurfaceTest {

    @Test
    void analyze_excludesDeviceWhoseCompromiseCannotChangeBehavior() {
        Map<String, DeviceSmvData> devices = new LinkedHashMap<>();
        devices.put("sensor_1", device("sensor_1", true));
        devices.put("light_1", device("light_1", false));
        devices.put("display_1", device("display_1", false));

        RuleDto rule = RuleDto.builder()
                .command(RuleDto.Command.builder().deviceName("light_1").action("turnOn").build())
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1").targetType("variable")
                        .attribute("reading").relation("=").value("alert").build()))
                .build();

        AttackSurface surface = AttackSurface.analyze(List.of(rule), devices);

        assertEquals(List.of("sensor_1", "light_1"), List.copyOf(surface.deviceVarNames()));
        assertEquals(2, surface.deviceCount());
        assertEquals(1, surface.falsifiableReadingDeviceCount());
        assertEquals(1, surface.automationLinkCount());
        assertEquals(3, surface.totalCount());
    }

    @Test
    void analyze_deduplicatesTargetWithFalsifiableReading() {
        Map<String, DeviceSmvData> devices = Map.of("hub_1", device("hub_1", true));
        RuleDto rule = RuleDto.builder()
                .command(RuleDto.Command.builder().deviceName("hub_1").action("refresh").build())
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("hub_1").targetType("variable")
                        .attribute("reading").relation("=").value("alert").build()))
                .build();

        AttackSurface surface = AttackSurface.analyze(List.of(rule), devices);

        assertEquals(1, surface.deviceCount());
        assertEquals(1, surface.falsifiableReadingDeviceCount());
        assertEquals(2, surface.totalCount());
    }

    @Test
    void analyze_usesCanonicalInstanceNameWhenMapContainsAliases() {
        DeviceSmvData sensor = device("sensor_1", true);
        Map<String, DeviceSmvData> devices = new LinkedHashMap<>();
        devices.put("sensor_1", sensor);
        devices.put("Sensor Template", sensor);

        AttackSurface surface = AttackSurface.analyze(List.of(), devices);

        assertEquals(List.of("sensor_1"), List.copyOf(surface.deviceVarNames()));
        assertEquals(1, surface.falsifiableReadingDeviceCount());
        assertEquals(1, surface.totalCount());
    }

    private DeviceSmvData device(String varName, boolean falsifiable) {
        DeviceManifest.InternalVariable variable = DeviceManifest.InternalVariable.builder()
                .name("reading")
                .isInside(true)
                .falsifiableWhenCompromised(falsifiable)
                .values(List.of("normal", "alert"))
                .build();
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName(varName);
        smv.setVariables(List.of(variable));
        return smv;
    }
}
