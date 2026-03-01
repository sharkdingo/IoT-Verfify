package cn.edu.nju.Iot_Verify.component.aitool.node;

import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.service.NodeService;
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
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.spy;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class NodeToolsErrorTest {

    @Mock
    private NodeService nodeService;
    @Mock
    private DeviceTemplateService deviceTemplateService;
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
        AddNodeTool tool = new AddNodeTool(nodeService, objectMapper, deviceTemplateService);
        when(nodeService.addNode(1L, "UnknownTemplate", null, null, null, null, null, null))
                .thenThrow(new BadRequestException("invalid template"));

        String result = tool.execute("{\"templateName\":\"UnknownTemplate\"}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("invalid template", json.path("error").asText());
        assertEquals("BUSINESS_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
    }

    @Test
    void deleteNodeTool_whenServiceThrowsBaseException_shouldReturnStructuredError() throws Exception {
        DeleteNodeTool tool = new DeleteNodeTool(nodeService, boardStorageService, objectMapper);
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(nodeService.deleteNode(1L, "ghost"))
                .thenThrow(new ResourceNotFoundException("not found"));

        String result = tool.execute("{\"label\":\"ghost\"}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("not found", json.path("error").asText());
        assertEquals("BUSINESS_ERROR", json.path("errorCode").asText());
        assertEquals(404, json.path("status").asInt());
    }

    @Test
    void addNodeTool_whenResponseSerializationFails_shouldReturnFallbackSuccess() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());
        AddNodeTool tool = new AddNodeTool(nodeService, failingMapper, deviceTemplateService);
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
        when(boardStorageService.getNodes(1L)).thenReturn(List.of());
        when(nodeService.deleteNode(1L, "ac_1"))
                .thenReturn("Deleted device successfully: ac_1");

        String result = tool.execute("{\"label\":\"ac_1\"}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("Deleted device successfully: ac_1", json.path("message").asText());
        assertTrue(json.path("warning").asText().contains("serialization degraded"));
    }
}
