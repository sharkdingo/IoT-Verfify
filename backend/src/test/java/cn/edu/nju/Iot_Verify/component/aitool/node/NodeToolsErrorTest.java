package cn.edu.nju.Iot_Verify.component.aitool.node;

import cn.edu.nju.Iot_Verify.dto.board.BoardBatchDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.NodeService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.ArgumentMatchers.isNull;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.spy;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class NodeToolsErrorTest {

    @Mock
    private NodeService nodeService;
    @Mock
    private BoardStorageService boardStorageService;

    private ObjectMapper objectMapper;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void addNodeTool_whenServiceThrowsBaseException_shouldReturnStructuredError() throws Exception {
        AddNodeTool tool = new AddNodeTool(nodeService, objectMapper);
        when(nodeService.addNode(1L, "UnknownTemplate", null, null, null, null, null, null))
                .thenThrow(new BadRequestException("invalid template"));

        String result = tool.execute("{\"templateName\":\"UnknownTemplate\"}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("invalid template", json.path("error").asText());
        assertEquals("BUSINESS_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
    }

    @Test
    void deleteNodeTool_whenDeviceMissing_shouldReturnStructuredError() throws Exception {
        DeleteNodeTool tool = new DeleteNodeTool(nodeService, boardStorageService, objectMapper);
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());

        String result = tool.execute("{\"label\":\"ghost\"}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("Device not found for deletion: 'ghost'.", json.path("error").asText());
        assertEquals("NOT_FOUND", json.path("errorCode").asText());
        assertEquals(404, json.path("status").asInt());
    }

    @Test
    void addNodeTool_whenResponseSerializationFails_shouldReturnFallbackSuccess() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());
        AddNodeTool tool = new AddNodeTool(nodeService, failingMapper);
        when(nodeService.addNode(1L, "Air Conditioner", null, null, null, null, null, null))
                .thenReturn("Created device successfully: ac_1.");

        String result = tool.execute("{\"templateName\":\"Air Conditioner\"}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("Created device successfully: ac_1.", json.path("message").asText());
        assertTrue(json.path("warning").asText().contains("serialization degraded"));
    }

    @Test
    void deleteNodeTool_whenResponseSerializationFails_shouldReturnFallbackSuccess() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());
        DeleteNodeTool tool = new DeleteNodeTool(nodeService, boardStorageService, failingMapper);
        DeviceNodeDto node = node("ac_1", "ac_1", "Light");
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(boardStorageService.saveBoardBatch(eq(1L), any(BoardBatchDto.class)))
                .thenReturn(new BoardBatchDto(List.of(), List.of(), List.of()));

        String result = tool.execute("{\"label\":\"ac_1\"}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("Device deleted successfully.", json.path("message").asText());
        assertTrue(json.path("warning").asText().contains("serialization degraded"));
    }

    @Test
    void deleteNodeTool_deletesNodeAndRelatedRulesSpecsAtomically() throws Exception {
        DeleteNodeTool tool = new DeleteNodeTool(nodeService, boardStorageService, objectMapper);
        DeviceNodeDto target = node("light_1", "KitchenLight", "Light");
        DeviceNodeDto variable = node("light_1_power", "power", "variable_power");
        DeviceNodeDto other = node("door_1", "Door", "Door");

        RuleDto relatedRule = RuleDto.builder()
                .id(10L)
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("KitchenLight")
                        .attribute("state")
                        .relation("=")
                        .value("on")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("Door")
                        .action("lock")
                        .build())
                .build();
        RuleDto remainingRule = RuleDto.builder()
                .id(11L)
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Door")
                        .attribute("state")
                        .relation("=")
                        .value("open")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("Door")
                        .action("close")
                        .build())
                .build();

        SpecificationDto relatedSpec = spec("spec-light", "light_1");
        SpecificationDto remainingSpec = spec("spec-door", "door_1");

        when(boardStorageService.getNodes(1L)).thenReturn(List.of(target, variable, other));
        when(boardStorageService.getRules(1L)).thenReturn(List.of(relatedRule, remainingRule));
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of(relatedSpec, remainingSpec));
        when(boardStorageService.saveBoardBatch(eq(1L), any(BoardBatchDto.class)))
                .thenReturn(new BoardBatchDto(List.of(other), List.of(remainingRule), List.of(remainingSpec)));

        String result = tool.execute("{\"identifier\":\"KitchenLight\"}");
        JsonNode json = objectMapper.readTree(result);

        ArgumentCaptor<BoardBatchDto> captor = ArgumentCaptor.forClass(BoardBatchDto.class);
        verify(boardStorageService).saveBoardBatch(eq(1L), captor.capture());
        BoardBatchDto batch = captor.getValue();

        assertEquals(List.of("door_1"), batch.getNodes().stream().map(DeviceNodeDto::getId).toList());
        assertEquals(List.of(11L), batch.getRules().stream().map(RuleDto::getId).toList());
        assertEquals(List.of("spec-door"), batch.getSpecs().stream().map(SpecificationDto::getId).toList());
        assertEquals(1, json.path("removedRules").asInt());
        assertEquals(1, json.path("removedSpecs").asInt());
    }

    private DeviceNodeDto node(String id, String label, String templateName) {
        DeviceNodeDto dto = new DeviceNodeDto();
        dto.setId(id);
        dto.setLabel(label);
        dto.setTemplateName(templateName);
        DeviceNodeDto.Position position = new DeviceNodeDto.Position();
        position.setX(0.0);
        position.setY(0.0);
        dto.setPosition(position);
        dto.setState("on");
        dto.setWidth(110);
        dto.setHeight(90);
        return dto;
    }

    private SpecificationDto spec(String id, String deviceId) {
        SpecificationDto dto = new SpecificationDto();
        dto.setId(id);
        dto.setTemplateId("2");
        dto.setTemplateLabel("Spec");

        SpecConditionDto condition = new SpecConditionDto();
        condition.setId(id + "-condition");
        condition.setSide("a");
        condition.setDeviceId(deviceId);
        condition.setDeviceLabel(deviceId);
        condition.setTargetType("state");
        condition.setKey("state");
        condition.setRelation("=");
        condition.setValue("on");

        dto.setAConditions(new ArrayList<>(List.of(condition)));
        dto.setIfConditions(new ArrayList<>());
        dto.setThenConditions(new ArrayList<>());
        dto.setDevices(new ArrayList<>());
        return dto;
    }
}
