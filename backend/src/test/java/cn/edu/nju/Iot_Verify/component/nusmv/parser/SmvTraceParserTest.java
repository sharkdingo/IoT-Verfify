package cn.edu.nju.Iot_Verify.component.nusmv.parser;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDeviceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceTrustPrivacyDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceVariableDto;
import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class SmvTraceParserTest {

    private final SmvTraceParser parser = new SmvTraceParser();

    @Test
    void parseCounterexample_parsesModeTrustPrivacyEnvAndFiltersInternalVars() {
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName("air_conditioner_1");
        smv.setTemplateName("Air Conditioner");
        smv.getModes().add("HvacMode");
        smv.getModeStates().put("HvacMode", List.of("cool", "heat"));
        smv.getStates().addAll(List.of("cool", "heat"));

        Map<String, DeviceSmvData> deviceMap = new LinkedHashMap<>();
        deviceMap.put("air_conditioner_1", smv);

        String counterexample = """
                -> State: 1.1 <-
                  air_conditioner_1.HvacMode = cool
                  air_conditioner_1.trust_HvacMode_cool = trusted
                  air_conditioner_1.trust_temperature = untrusted
                  air_conditioner_1.temperature = 25
                  air_conditioner_1.temperature_rate = -1
                  air_conditioner_1.is_attack = FALSE
                  air_conditioner_1.cool_a = TRUE
                  air_conditioner_1.privacy_photo = private
                  a_temperature = 25
                -> State: 1.2 <-
                  air_conditioner_1.HvacMode = heat
                  a_temperature = 24
                """;

        List<TraceStateDto> states = parser.parseCounterexampleStates(counterexample, deviceMap);

        assertEquals(2, states.size());

        TraceStateDto s1 = states.get(0);
        TraceDeviceDto d1 = s1.getDevices().get(0);
        assertEquals("cool", d1.getNewState());
        assertEquals("Air Conditioner", d1.getTemplateName());
        assertEquals("air_conditioner_1", d1.getDeviceLabel());

        TraceVariableDto temp = findVariable(d1, "temperature");
        assertNotNull(temp);
        assertEquals("25", temp.getValue());
        assertEquals("untrusted", temp.getTrust());
        assertNull(findVariable(d1, "temperature_rate"));
        assertNull(findVariable(d1, "is_attack"));
        assertNull(findVariable(d1, "cool_a"));

        TraceTrustPrivacyDto trust = findTrust(d1, "HvacMode_cool");
        assertNotNull(trust);
        assertTrue(Boolean.TRUE.equals(trust.getTrust()));

        TraceTrustPrivacyDto privacy = findPrivacy(d1, "photo");
        assertNotNull(privacy);
        assertEquals("private", privacy.getPrivacy());

        assertEquals("25", findEnvValue(s1, "a_temperature"));
        assertEquals("24", findEnvValue(states.get(1), "a_temperature"));
        assertEquals("heat", states.get(1).getDevices().get(0).getNewState());
    }

    @Test
    void parseCounterexample_combinesMultiModeStatesByModeOrder() {
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName("thermostat_1");
        smv.setTemplateName("Thermostat");
        smv.getModes().addAll(List.of("Mode", "ThermostatFanMode"));

        Map<String, DeviceSmvData> deviceMap = new LinkedHashMap<>();
        deviceMap.put("thermostat_1", smv);

        String counterexample = """
                -> State: 1.1 <-
                  thermostat_1.ThermostatFanMode = on
                  thermostat_1.Mode = auto
                """;

        List<TraceStateDto> states = parser.parseCounterexampleStates(counterexample, deviceMap);
        assertEquals(1, states.size());
        assertEquals("auto;on", states.get(0).getDevices().get(0).getNewState());
    }

    @Test
    void parseCounterexample_backfillsMissingModeFromPreviousState() {
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName("thermostat_1");
        smv.setTemplateName("Thermostat");
        smv.getModes().addAll(List.of("Mode", "ThermostatFanMode"));

        Map<String, DeviceSmvData> deviceMap = new LinkedHashMap<>();
        deviceMap.put("thermostat_1", smv);

        String counterexample = """
                -> State: 1.1 <-
                  thermostat_1.Mode = auto
                  thermostat_1.ThermostatFanMode = on
                -> State: 1.2 <-
                  thermostat_1.Mode = heat
                """;

        List<TraceStateDto> states = parser.parseCounterexampleStates(counterexample, deviceMap);
        assertEquals(2, states.size());
        assertEquals("auto;on", states.get(0).getDevices().get(0).getNewState());
        assertEquals("heat;on", states.get(1).getDevices().get(0).getNewState());
    }

    @Test
    void parseCounterexample_handlesTraceNumberGreaterThanOne() {
        // NuSMV may output "State 2.1" for the second trace; parser should handle \d+\.\d+
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName("air_conditioner_1");
        smv.setTemplateName("Air Conditioner");
        smv.getModes().add("HvacMode");
        smv.getModeStates().put("HvacMode", List.of("cool", "heat"));
        smv.getStates().addAll(List.of("cool", "heat"));

        Map<String, DeviceSmvData> deviceMap = new LinkedHashMap<>();
        deviceMap.put("air_conditioner_1", smv);

        String counterexample = """
                -> State: 2.1 <-
                  air_conditioner_1.HvacMode = cool
                  air_conditioner_1.temperature = 30
                -> State: 2.2 <-
                  air_conditioner_1.HvacMode = heat
                  air_conditioner_1.temperature = 28
                """;

        List<TraceStateDto> states = parser.parseCounterexampleStates(counterexample, deviceMap);
        assertEquals(2, states.size());
        assertEquals(1, states.get(0).getStateIndex());
        assertEquals(2, states.get(1).getStateIndex());
        assertEquals("cool", states.get(0).getDevices().get(0).getNewState());
        assertEquals("heat", states.get(1).getDevices().get(0).getNewState());
    }

    @Test
    void parseCounterexample_doesNotMatchStateMidLine() {
        // Ensure anchored regex doesn't match "State" appearing mid-line
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName("dev1");
        smv.setTemplateName("Device");

        Map<String, DeviceSmvData> deviceMap = new LinkedHashMap<>();
        deviceMap.put("dev1", smv);

        String counterexample = """
                -> State: 1.1 <-
                  dev1.status = on
                some text mentioning State: 1.99 in the middle
                -> State: 1.2 <-
                  dev1.status = off
                """;

        List<TraceStateDto> states = parser.parseCounterexampleStates(counterexample, deviceMap);
        // Should only parse 2 states (1.1 and 1.2), not the mid-line "State: 1.99"
        assertEquals(2, states.size());
        assertEquals(1, states.get(0).getStateIndex());
        assertEquals(2, states.get(1).getStateIndex());
    }

    private TraceVariableDto findVariable(TraceDeviceDto dev, String name) {
        if (dev.getVariables() == null) {
            return null;
        }
        return dev.getVariables().stream().filter(v -> name.equals(v.getName())).findFirst().orElse(null);
    }

    private TraceTrustPrivacyDto findTrust(TraceDeviceDto dev, String name) {
        if (dev.getTrustPrivacy() == null) {
            return null;
        }
        return dev.getTrustPrivacy().stream().filter(v -> name.equals(v.getName())).findFirst().orElse(null);
    }

    private TraceTrustPrivacyDto findPrivacy(TraceDeviceDto dev, String name) {
        if (dev.getPrivacies() == null) {
            return null;
        }
        return dev.getPrivacies().stream().filter(v -> name.equals(v.getName())).findFirst().orElse(null);
    }

    private String findEnvValue(TraceStateDto state, String name) {
        if (state.getEnvVariables() == null) {
            return null;
        }
        return state.getEnvVariables().stream()
                .filter(v -> name.equals(v.getName()))
                .map(TraceVariableDto::getValue)
                .findFirst()
                .orElse(null);
    }
}
