package cn.edu.nju.Iot_Verify.component.aitool.board;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class BoardOverviewToolTest {

    @Mock
    private BoardStorageService boardStorageService;

    private ObjectMapper objectMapper;
    private BoardOverviewTool tool;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        tool = new BoardOverviewTool(boardStorageService, objectMapper);
        UserContextHolder.clear();
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void execute_withoutLogin_shouldReturnErrorJson() throws Exception {
        String result = tool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("UNAUTHORIZED", json.path("errorCode").asText());
        assertEquals(401, json.path("status").asInt());
    }

    @Test
    void execute_withUnknownField_shouldRejectBeforeReadingBoard() throws Exception {
        UserContextHolder.setUserId(1L);
        JsonNode json = objectMapper.readTree(tool.execute("{\"includeRaw\":true}"));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        verify(boardStorageService, never()).getNodes(1L);
    }

    @Test
    void execute_shouldDeriveEdgeSummaryFromRules() throws Exception {
        UserContextHolder.setUserId(1L);

        DeviceNodeDto light = new DeviceNodeDto();
        light.setId("n1");
        light.setLabel("Light");
        light.setTemplateName("LightTemplate");
        light.setState("off");
        light.setCurrentStateTrust("untrusted");
        light.setCurrentStatePrivacy("private");
        light.setVariables(List.of(new VariableStateDto("brightness", "20", "trusted")));
        light.setPrivacies(List.of(new PrivacyStateDto("brightness", "private")));

        DeviceNodeDto sensor = new DeviceNodeDto();
        sensor.setId("n2");
        sensor.setLabel("Sensor");
        sensor.setTemplateName("SensorTemplate");
        sensor.setState("idle");

        RuleDto rule = RuleDto.builder()
                .id(1L)
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("n1")
                        .attribute("state")
                        .targetType("state")
                        .relation("=")
                        .value("on")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("n2")
                        .action("turnOn")
                        .build())
                .build();

        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_1");
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        SpecConditionDto specCondition = new SpecConditionDto();
        specCondition.setDeviceId("n1");
        specCondition.setDeviceLabel("stale label");
        specCondition.setTargetType("state");
        specCondition.setKey("state");
        specCondition.setRelation("=");
        specCondition.setValue("on");
        spec.setAConditions(List.of(specCondition));
        spec.setIfConditions(List.of());
        spec.setThenConditions(List.of());
        spec.setFormula("CTLSPEC AG(n1.state = on)");

        when(boardStorageService.getNodes(1L)).thenReturn(List.of(light, sensor));
        when(boardStorageService.getEnvironmentVariables(1L)).thenReturn(List.of(
                new BoardEnvironmentVariableDto("temperature", "28", "untrusted", "private")));
        when(boardStorageService.getRules(1L)).thenReturn(List.of(rule));
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of(spec));

        String result = tool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(2, json.path("deviceCount").asInt());
        assertEquals(1, json.path("environmentVariableCount").asInt());
        assertEquals("untrusted", json.path("devices").get(0).path("currentStateTrust").asText());
        assertEquals("private", json.path("devices").get(0).path("currentStatePrivacy").asText());
        assertEquals("brightness", json.path("devices").get(0).path("variables").get(0).path("name").asText());
        assertEquals("temperature", json.path("environmentVariables").get(0).path("name").asText());
        assertEquals(1, json.path("edgeCount").asInt());
        assertFalse(json.path("edges").get(0).has("id"));
        assertFalse(json.path("edges").get(0).has("ruleId"));
        assertFalse(json.path("edges").get(0).has("conditionIndex"));
        assertFalse(json.path("rules").get(0).has("id"));
        assertFalse(json.path("specs").get(0).has("id"));
        assertFalse(json.path("specs").get(0).has("formula"));
        assertEquals("n1", json.path("edges").get(0).path("from").asText());
        assertEquals("n2", json.path("edges").get(0).path("to").asText());
        assertEquals("Light", json.path("edges").get(0).path("fromLabel").asText());
        assertEquals("Sensor", json.path("edges").get(0).path("toLabel").asText());
        assertEquals("state", json.path("edges").get(0).path("sourceAttribute").asText());
        assertEquals("turnOn", json.path("edges").get(0).path("targetAction").asText());
        assertEquals("n1", json.path("rules").get(0).path("conditions").get(0).path("deviceId").asText());
        assertEquals("Light", json.path("rules").get(0).path("conditions").get(0).path("deviceLabel").asText());
        assertEquals("Light.state = on", json.path("rules").get(0).path("conditions").get(0).path("summary").asText());
        assertEquals("Sensor", json.path("rules").get(0).path("command").path("deviceLabel").asText());
        assertEquals("IF Light.state = on THEN Sensor.turnOn",
                json.path("rules").get(0).path("description").asText());
        assertFalse(json.path("rules").get(0).path("description").asText().contains("n1"));
        assertEquals("Light", json.path("specs").get(0).path("aConditions").get(0).path("deviceLabel").asText());
        assertEquals("Light state = on", json.path("specs").get(0).path("aConditions").get(0).path("summary").asText());
        assertEquals("CTL AG(\"Light\".state = \"on\")",
                json.path("specs").get(0).path("formulaPreview").asText());
        assertFalse(json.path("specs").get(0).path("formulaPreview").asText().contains("n1"));
    }
}
