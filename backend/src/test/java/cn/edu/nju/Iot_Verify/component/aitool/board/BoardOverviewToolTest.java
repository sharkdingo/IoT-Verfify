package cn.edu.nju.Iot_Verify.component.aitool.board;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
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
    void execute_shouldDeriveEdgeSummaryFromRules() throws Exception {
        UserContextHolder.setUserId(1L);

        DeviceNodeDto light = new DeviceNodeDto();
        light.setId("n1");
        light.setLabel("Light");
        light.setTemplateName("LightTemplate");
        light.setState("off");

        DeviceNodeDto sensor = new DeviceNodeDto();
        sensor.setId("n2");
        sensor.setLabel("Sensor");
        sensor.setTemplateName("SensorTemplate");
        sensor.setState("idle");

        RuleDto rule = RuleDto.builder()
                .id(1L)
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Light")
                        .attribute("state")
                        .relation("=")
                        .value("on")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("Sensor")
                        .action("turnOn")
                        .build())
                .build();

        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_1");
        spec.setTemplateId("A1");
        spec.setTemplateLabel("Always");
        spec.setAConditions(List.of());
        spec.setIfConditions(List.of());
        spec.setThenConditions(List.of());

        when(boardStorageService.getNodes(1L)).thenReturn(List.of(light, sensor));
        when(boardStorageService.getRules(1L)).thenReturn(List.of(rule));
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of(spec));

        String result = tool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(2, json.path("deviceCount").asInt());
        assertEquals(1, json.path("edgeCount").asInt());
        assertEquals("rule_1_condition_0", json.path("edges").get(0).path("id").asText());
        assertEquals("n1", json.path("edges").get(0).path("from").asText());
        assertEquals("n2", json.path("edges").get(0).path("to").asText());
        assertEquals("Light", json.path("edges").get(0).path("fromLabel").asText());
        assertEquals("Sensor", json.path("edges").get(0).path("toLabel").asText());
        assertEquals("state", json.path("edges").get(0).path("sourceAttribute").asText());
        assertEquals("turnOn", json.path("edges").get(0).path("targetAction").asText());
        verify(boardStorageService, never()).getEdges(1L);
    }
}
