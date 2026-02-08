package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.component.nusmv.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.trace.*;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.*;

import static org.junit.jupiter.api.Assertions.*;

/**
 * 集成测试 - 使用真实 NuSMV 输出的 Counterexample 解析
 * 
 * 这些测试使用从实际 NuSMV 工具生成的 counterexample 格式
 * 参考: NuSMV 2.x counterexample output format
 */
class NuSMVIntegrationTest {

    private Map<String, DeviceSmvData> deviceSmvMap;
    private final SmvTraceParser traceParser = new SmvTraceParser();

    @BeforeEach
    void setUp() {
        deviceSmvMap = createRealisticDeviceSmvMap();
    }

    // ==================== 真实 NuSMV Counterexample 格式测试 ====================

    @Test
    @DisplayName("集成测试 - 解析真实 NuSMV counterexample 格式（状态机模型）")
    void parseCounterexample_RealNuSMVFormat_StateMachine() {
        // 这是一个典型的 NuSMV 状态机 counterexample 格式
        String counterexample = """
            -- specification AG (state = on) is false
            -- as demonstrated by the following execution sequence
            Trace 1:    2.0
            State 1.1:
              sensor_1.state = off
              sensor_1.temp = 20
              sensor_1.trust_off = trusted
              sensor_1.privacy_temp = public
            State 1.2:
              sensor_1.state = on
              sensor_1.temp = 20
              sensor_1.trust_on = trusted
              sensor_1.privacy_temp = public
            State 1.3:
              sensor_1.state = error
              sensor_1.temp = 100
              sensor_1.trust_error = untrusted
              sensor_1.privacy_temp = private
            """;
        
        List<TraceStateDto> states = traceParser.parseCounterexampleStates(counterexample, deviceSmvMap);
        
        assertEquals(3, states.size(), "Should have 3 states in trace");
        assertEquals(1, states.get(0).getStateIndex());
        assertEquals(2, states.get(1).getStateIndex());
        assertEquals(3, states.get(2).getStateIndex());
    }

    @Test
    @DisplayName("集成测试 - 解析多设备 NuSMV counterexample")
    void parseCounterexample_MultiDeviceNuSMV() {
        String counterexample = """
            -- specification AG (device1.state = idle & device1.state = idle) is false
            -- as demonstrated by the following execution sequence
            Trace 1:    3.0
            State 1.1:
              device_1.state = running
              device_1.value = 50
              device_1.state = idle
              device_1.value = 0
            State 1.2:
              device_1.state = idle
              device_1.value = 50
              device_1.state = running
              device_1.value = 100
            """;
        
        List<TraceStateDto> states = traceParser.parseCounterexampleStates(counterexample, deviceSmvMap);
        
        assertEquals(2, states.size());
    }

    @Test
    @DisplayName("集成测试 - 解析包含变量的 NuSMV counterexample")
    void parseCounterexample_WithVariables() {
        String counterexample = """
            Trace 1:    2.0
            State 1.1:
              thermostat_1.mode = heat
              thermostat_1.temperature = 20
              thermostat_1.humidity = 45
              thermostat_1.trust_heat = trusted
            State 1.2:
              thermostat_1.mode = cool
              thermostat_1.temperature = 22
              thermostat_1.humidity = 50
              thermostat_1.trust_cool = trusted
            """;
        
        List<TraceStateDto> states = traceParser.parseCounterexampleStates(counterexample, deviceSmvMap);
        
        assertEquals(2, states.size());
        assertNotNull(states.get(0).getDevices());
    }

    @Test
    @DisplayName("集成测试 - 解析带注释的 NuSMV 输出")
    void parseCounterexample_WithComments() {
        String counterexample = """
            -- This is a comment line
            -- Another comment
            State 1.1:   -- inline comment
              device_1.state = running
            -- Comment between states
            State 1.2:
              device_1.state = idle
            """;
        
        List<TraceStateDto> states = traceParser.parseCounterexampleStates(counterexample, deviceSmvMap);
        
        assertEquals(2, states.size());
        // 状态名称会匹配到设备
        assertNotNull(states.get(0).getDevices());
        if (!states.get(0).getDevices().isEmpty()) {
            assertEquals("running", states.get(0).getDevices().get(0).getNewState());
            assertEquals("idle", states.get(1).getDevices().get(0).getNewState());
        }
    }

    @Test
    @DisplayName("集成测试 - 解析隐私属性 counterexample")
    void parseCounterexample_PrivacyProperties() {
        String counterexample = """
            -- specification AG (privacy_location = private) is false
            Trace 1:    4.0
            State 1.1:
              device_1.location = home
              device_1.privacy_location = public
              device_1.trust_home = trusted
            State 1.2:
              device_1.location = away
              device_1.privacy_location = public
              device_1.trust_away = trusted
            State 1.3:
              device_1.location = work
              device_1.privacy_location = private
              device_1.trust_work = untrusted
            """;
        
        List<TraceStateDto> states = traceParser.parseCounterexampleStates(counterexample, deviceSmvMap);
        
        assertEquals(3, states.size());
    }

    @Test
    @DisplayName("集成测试 - 解析违反规格的反例")
    void parseCounterexample_ViolatedSpec() {
        String counterexample = """
            -- ***************************************
            --   as demonstrated by the following execution sequence
            --   which witnesses the violation of the property
            -- ***************************************
            Trace 1:    5.0
            State 1.1:
              sensor_1.sensor_state = normal
              sensor_1.value = 10
            State 1.2:
              sensor_1.sensor_state = normal
              sensor_1.value = 15
            State 1.3:
              sensor_1.sensor_state = high
              sensor_1.value = 25
            State 1.4:
              sensor_1.sensor_state = critical
              sensor_1.value = 50
            State 1.5:
              sensor_1.sensor_state = error
              sensor_1.value = 100
            """;
        
        List<TraceStateDto> states = traceParser.parseCounterexampleStates(counterexample, deviceSmvMap);
        
        assertEquals(5, states.size());
        assertEquals(1, states.get(0).getStateIndex());
        assertEquals(5, states.get(4).getStateIndex());
    }

    // ==================== 边界情况测试 ====================

    @Test
    @DisplayName("集成测试 - 解析超长 counterexample（性能测试）")
    void parseCounterexample_LongTrace_Performance() {
        StringBuilder sb = new StringBuilder();
        sb.append("Trace 1:    ").append(100).append(".0\n");
        
        for (int i = 1; i <= 100; i++) {
            sb.append("State 1.").append(i).append(":\n");
            sb.append("  device_1.state = state").append(i % 3).append("\n");
            sb.append("  device_1.value = ").append(i).append("\n");
        }
        
        String counterexample = sb.toString();
        
        long startTime = System.nanoTime();
        List<TraceStateDto> states = traceParser.parseCounterexampleStates(counterexample, deviceSmvMap);
        long duration = System.nanoTime() - startTime;
        
        assertEquals(100, states.size());
        assertTrue(duration < 1_000_000_000, "Should parse 100 states in under 1 second");
    }

    @Test
    @DisplayName("集成测试 - 解析包含特殊字符值的 counterexample")
    void parseCounterexample_SpecialCharacters() {
        String counterexample = """
            State 1.1:
              device_1.state = initial_state
              device_1.mode = MODE_HIGH
              device_1.trust_initial = trusted
            State 1.2:
              device_1.state = final-state
              device_1.mode = mode-low
              device_1.trust_final = untrusted
            """;
        
        List<TraceStateDto> states = traceParser.parseCounterexampleStates(counterexample, deviceSmvMap);
        
        assertEquals(2, states.size());
    }

    @Test
    @DisplayName("集成测试 - 解析空行和空白字符")
    void parseCounterexample_WhitespaceHandling() {
        String counterexample = """
            
            
            State 1.1:
              device_1.state = on
            
            
            State 1.2:
              device_1.state = off
            
            
            """;
        
        List<TraceStateDto> states = traceParser.parseCounterexampleStates(counterexample, deviceSmvMap);
        
        assertEquals(2, states.size());
    }

    @Test
    @DisplayName("集成测试 - 解析没有变量行的状态")
    void parseCounterexample_StatesWithoutVariables() {
        String counterexample = """
            State 1.1:
            State 1.2:
            State 1.3:
            """;
        
        List<TraceStateDto> states = traceParser.parseCounterexampleStates(counterexample, deviceSmvMap);
        
        assertEquals(3, states.size());
    }

    // ==================== 辅助方法 ====================

    /**
     * 创建真实的设备 SMV 数据映射
     */
    private Map<String, DeviceSmvData> createRealisticDeviceSmvMap() {
        Map<String, DeviceSmvData> smvDataMap = new HashMap<>();
        
        // 创建 sensor 设备
        DeviceSmvData sensor = new DeviceSmvData();
        sensor.id = "sensor1";
        sensor.name = "sensor";
        sensor.deviceNo = 1;
        sensor.states = new ArrayList<>(List.of("off", "on", "error", "normal", "high", "critical"));
        sensor.stateTrust.put("off", "trusted");
        sensor.stateTrust.put("on", "trusted");
        sensor.stateTrust.put("error", "untrusted");
        sensor.stateTrust.put("normal", "trusted");
        sensor.stateTrust.put("high", "trusted");
        sensor.stateTrust.put("critical", "untrusted");
        sensor.contentPrivacy.put("temp", "public");
        smvDataMap.put("sensor1", sensor);
        
        // 创建 device 设备
        DeviceSmvData device = new DeviceSmvData();
        device.id = "device1";
        device.name = "device";
        device.deviceNo = 1;
        device.states = new ArrayList<>(List.of("idle", "running", "active", "inactive", "initial_state", "final-state"));
        device.stateTrust.put("idle", "trusted");
        device.stateTrust.put("running", "trusted");
        device.stateTrust.put("active", "trusted");
        device.stateTrust.put("inactive", "trusted");
        device.stateTrust.put("initial_state", "trusted");
        device.stateTrust.put("final-state", "untrusted");
        device.contentPrivacy.put("location", "public");
        device.contentPrivacy.put("mode", "public");
        smvDataMap.put("device1", device);
        
        // 创建 thermostat 设备
        DeviceSmvData thermostat = new DeviceSmvData();
        thermostat.id = "thermostat1";
        thermostat.name = "thermostat";
        thermostat.deviceNo = 1;
        thermostat.states = new ArrayList<>(List.of("heat", "cool", "off"));
        thermostat.stateTrust.put("heat", "trusted");
        thermostat.stateTrust.put("cool", "trusted");
        thermostat.stateTrust.put("off", "trusted");
        smvDataMap.put("thermostat1", thermostat);
        
        return smvDataMap;
    }
}
