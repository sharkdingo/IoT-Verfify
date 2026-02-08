package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.component.nusmv.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.data.TemplateWrapper;
import cn.edu.nju.Iot_Verify.dto.trace.*;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.util.*;

import static org.junit.jupiter.api.Assertions.*;

/**
 * 单元测试 - SmvTraceParser 边缘情况
 */
class ServiceImplEdgeCaseTest {

    private final SmvTraceParser traceParser = new SmvTraceParser();

    @Test
    @DisplayName("TraceParser - 空 counterexample 返回空列表")
    void parseCounterexample_EmptyInput_ReturnsEmptyList() {
        List<TraceStateDto> result = traceParser.parseCounterexampleStates("", null);
        assertTrue(result.isEmpty());
    }

    @Test
    @DisplayName("TraceParser - null counterexample 返回空列表")
    void parseCounterexample_NullInput_ReturnsEmptyList() {
        List<TraceStateDto> result = traceParser.parseCounterexampleStates(null, null);
        assertTrue(result.isEmpty());
    }

    @Test
    @DisplayName("TraceParser - 无 State 行的 counterexample 返回空列表")
    void parseCounterexample_NoStateLines_ReturnsEmptyList() {
        String counterexample = "module.var = value\nmodule.state = State1";
        List<TraceStateDto> result = traceParser.parseCounterexampleStates(counterexample, new HashMap<>());
        assertTrue(result.isEmpty());
    }

    @Test
    @DisplayName("TraceParser - 单个状态解析正确")
    void parseCounterexample_SingleState_ParsesCorrectly() {
        String counterexample = "State 1.1: s1\n  device.var = 5";
        Map<String, DeviceSmvData> smvDataMap = createTestSmvDataMap();
        
        List<TraceStateDto> result = traceParser.parseCounterexampleStates(counterexample, smvDataMap);
        
        assertEquals(1, result.size());
        assertEquals(1, result.get(0).getStateIndex());
        assertEquals(1, result.get(0).getDevices().size());
        assertEquals("s1", result.get(0).getDevices().get(0).getNewState());
    }

    @Test
    @DisplayName("TraceParser - 多个状态解析正确")
    void parseCounterexample_MultipleStates_ParsesCorrectly() {
        String counterexample = "State 1.1: s1\n  module.var = 5\nState 1.2: s2\n  module.var = 10";
        Map<String, DeviceSmvData> smvDataMap = createTestSmvDataMap();
        
        List<TraceStateDto> result = traceParser.parseCounterexampleStates(counterexample, smvDataMap);
        
        assertEquals(2, result.size());
        assertEquals(1, result.get(0).getStateIndex());
        assertEquals(2, result.get(1).getStateIndex());
    }

    @Test
    @DisplayName("TraceParser - 变量值解析正确")
    void parseCounterexample_VariableValues_ParsesCorrectly() {
        String counterexample = "State 1.1: s1\n  device1.var1 = 10\n  device1.var2 = true";
        Map<String, DeviceSmvData> smvDataMap = createTestSmvDataMap();
        
        List<TraceStateDto> result = traceParser.parseCounterexampleStates(counterexample, smvDataMap);
        
        assertEquals(1, result.size());
        assertNotNull(result.get(0).getDevices());
    }

    @Test
    @DisplayName("TraceParser - 未知状态名不匹配任何设备")
    void parseCounterexample_UnknownState_NoMatch() {
        String counterexample = "State 1.1: unknown_state\n  module.var = 5";
        Map<String, DeviceSmvData> smvDataMap = createTestSmvDataMap();
        
        List<TraceStateDto> result = traceParser.parseCounterexampleStates(counterexample, smvDataMap);
        
        assertEquals(1, result.size());
        assertTrue(result.get(0).getDevices().isEmpty());
    }

    @Test
    @DisplayName("TraceParser - 空 smvDataMap 不影响解析")
    void parseCounterexample_EmptySmvDataMap_ParsesWithoutError() {
        String counterexample = "State 1.1: s1\n  module.var = 5";
        
        List<TraceStateDto> result = traceParser.parseCounterexampleStates(counterexample, new HashMap<>());
        
        assertEquals(1, result.size());
        assertTrue(result.get(0).getDevices().isEmpty());
    }

    // ==================== DeviceSmvData Tests ====================

    @Test
    @DisplayName("DeviceSmvData - 正确初始化")
    void deviceSmvData_Initialization_Correct() {
        DeviceSmvData smv = new DeviceSmvData();
        smv.setId("test-id");
        smv.setName("TestTemplate");
        smv.setDeviceNo(1);
        
        assertEquals("test-id", smv.getId());
        assertEquals("TestTemplate", smv.getName());
        assertEquals(1, smv.getDeviceNo());
        assertNotNull(smv.getStates());
        assertNotNull(smv.getVariables());
        assertNotNull(smv.getTransitions());
        assertNotNull(smv.getVariableValues());
        assertNotNull(smv.getStateTrust());
        assertNotNull(smv.getContentPrivacy());
        assertNotNull(smv.getImpactedVariables());
        assertNotNull(smv.getContents());
        assertNotNull(smv.getStateDynamics());
    }

    @Test
    @DisplayName("DeviceSmvData - 状态动态信息存储正确")
    void deviceSmvData_StateDynamics_StoredCorrectly() {
        DeviceSmvData smv = new DeviceSmvData();
        Map<String, String> dynamics = new HashMap<>();
        dynamics.put("temperature", "1");
        
        smv.getStateDynamics().put("working", dynamics);
        
        assertTrue(smv.getStateDynamics().containsKey("working"));
        assertEquals("1", smv.getStateDynamics().get("working").get("temperature"));
    }

    // ==================== TemplateWrapper Tests ====================

    @Test
    @DisplayName("TemplateWrapper - 正确初始化")
    void templateWrapper_Initialization_Correct() {
        TemplateWrapper wrapper = new TemplateWrapper();
        assertNull(wrapper.getTemplatePo());
        assertNull(wrapper.getManifest());
    }

    // ==================== 辅助方法 ====================

    private Map<String, DeviceSmvData> createTestSmvDataMap() {
        Map<String, DeviceSmvData> smvDataMap = new HashMap<>();
        
        DeviceSmvData smv = new DeviceSmvData();
        smv.setId("device1");
        smv.setName("device");
        smv.setDeviceNo(1);
        smv.setStates(new ArrayList<>(List.of("s1", "s2")));
        
        smvDataMap.put("device1", smv);
        
        return smvDataMap;
    }
}
