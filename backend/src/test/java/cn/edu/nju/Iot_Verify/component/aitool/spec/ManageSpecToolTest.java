package cn.edu.nju.Iot_Verify.component.aitool.spec;

import cn.edu.nju.Iot_Verify.dto.device.DeviceNodeDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.spy;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ManageSpecToolTest {

    @Mock
    private BoardStorageService boardStorageService;

    private ManageSpecTool tool;

    @BeforeEach
    void setUp() {
        tool = new ManageSpecTool(boardStorageService, new ObjectMapper());
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void add_withUnknownTemplateId_shouldReject() {
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("dev_1");
        node.setLabel("Device1");
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node));

        String argsJson = """
                {
                  "action":"add",
                  "templateId":"99",
                  "aConditions":[
                    {
                      "deviceId":"dev_1",
                      "targetType":"state",
                      "key":"state",
                      "relation":"=",
                      "value":"On"
                    }
                  ]
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("Unsupported templateId"));
        verify(boardStorageService, never()).saveSpecs(anyLong(), any());
    }

    @Test
    void add_withDeviceLabelOnly_shouldResolveToDeviceId() {
        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("ac_1");
        node.setLabel("LivingRoomAC");
        node.setTemplateName("Air Conditioner");
        node.setState("Working");
        node.setWidth(100);
        node.setHeight(80);
        DeviceNodeDto.Position position = new DeviceNodeDto.Position();
        position.setX(10.0);
        position.setY(20.0);
        node.setPosition(position);

        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node));
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(boardStorageService.saveSpecs(eq(1L), any())).thenAnswer(invocation -> invocation.getArgument(1));

        String argsJson = """
                {
                  "action":"add",
                  "templateId":"1",
                  "aConditions":[
                    {
                      "deviceLabel":"LivingRoomAC",
                      "targetType":"state",
                      "key":"state",
                      "relation":"=",
                      "value":"On"
                    }
                  ]
                }
                """;

        String result = tool.execute(argsJson);
        assertTrue(result.contains("Specification added successfully."));

        @SuppressWarnings("unchecked")
        ArgumentCaptor<List<SpecificationDto>> captor =
                ArgumentCaptor.forClass((Class<List<SpecificationDto>>) (Class<?>) List.class);
        verify(boardStorageService).saveSpecs(eq(1L), captor.capture());
        List<SpecificationDto> savedSpecs = captor.getValue();
        assertEquals(1, savedSpecs.size());
        assertEquals("ac_1", savedSpecs.get(0).getAConditions().get(0).getDeviceId());
        assertEquals("LivingRoomAC", savedSpecs.get(0).getAConditions().get(0).getDeviceLabel());
    }

    @Test
    void add_withAmbiguousDeviceLabel_shouldRejectAndNotSave() {
        DeviceNodeDto node1 = new DeviceNodeDto();
        node1.setId("ac_1");
        node1.setLabel("LivingRoomAC");

        DeviceNodeDto node2 = new DeviceNodeDto();
        node2.setId("ac_2");
        node2.setLabel("LivingRoomAC");

        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node1, node2));

        String argsJson = """
                {
                  "action":"add",
                  "templateId":"1",
                  "aConditions":[
                    {
                      "deviceLabel":"LivingRoomAC",
                      "targetType":"state",
                      "key":"state",
                      "relation":"=",
                      "value":"On"
                    }
                  ]
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("ambiguous deviceLabel"));
        verify(boardStorageService, never()).saveSpecs(anyLong(), any());
    }

    @Test
    void add_withInconsistentDeviceIdAndDeviceLabel_shouldRejectAndNotSave() {
        DeviceNodeDto node1 = new DeviceNodeDto();
        node1.setId("ac_1");
        node1.setLabel("LivingRoomAC");

        DeviceNodeDto node2 = new DeviceNodeDto();
        node2.setId("ac_2");
        node2.setLabel("KitchenAC");

        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node1, node2));

        String argsJson = """
                {
                  "action":"add",
                  "templateId":"1",
                  "aConditions":[
                    {
                      "deviceId":"ac_1",
                      "deviceLabel":"KitchenAC",
                      "targetType":"state",
                      "key":"state",
                      "relation":"=",
                      "value":"On"
                    }
                  ]
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("inconsistent deviceId/deviceLabel"));
        verify(boardStorageService, never()).saveSpecs(anyLong(), any());
    }

    @Test
    void execute_whenJsonSerializationFails_shouldReturnStableErrorJson() throws Exception {
        ObjectMapper failingMapper = mock(ObjectMapper.class);
        when(failingMapper.writeValueAsString(any())).thenThrow(new JsonProcessingException("boom") {
        });

        ManageSpecTool fallbackTool = new ManageSpecTool(boardStorageService, failingMapper);
        UserContextHolder.clear();

        String result = fallbackTool.execute("{}");

        JsonNode json = new ObjectMapper().readTree(result);
        assertEquals("User not logged in", json.path("error").asText());
        assertEquals("UNAUTHORIZED", json.path("errorCode").asText());
        assertEquals(401, json.path("status").asInt());
    }

    @Test
    void add_whenResponseSerializationFails_shouldReturnFallbackSuccess() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());

        ManageSpecTool fallbackTool = new ManageSpecTool(boardStorageService, failingMapper);

        DeviceNodeDto node = new DeviceNodeDto();
        node.setId("ac_1");
        node.setLabel("LivingRoomAC");
        when(boardStorageService.getNodes(1L)).thenReturn(List.of(node));
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of());
        when(boardStorageService.saveSpecs(eq(1L), any())).thenAnswer(invocation -> invocation.getArgument(1));

        String argsJson = """
                {
                  "action":"add",
                  "templateId":"1",
                  "aConditions":[
                    {
                      "deviceId":"ac_1",
                      "targetType":"state",
                      "key":"state",
                      "relation":"=",
                      "value":"On"
                    }
                  ]
                }
                """;

        String result = fallbackTool.execute(argsJson);
        JsonNode json = new ObjectMapper().readTree(result);

        assertEquals("Specification added successfully.", json.path("message").asText());
        assertTrue(json.path("warning").asText().contains("serialization degraded"));
    }
}
