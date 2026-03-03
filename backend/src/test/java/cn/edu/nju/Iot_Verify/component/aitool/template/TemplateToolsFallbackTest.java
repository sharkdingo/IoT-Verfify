package cn.edu.nju.Iot_Verify.component.aitool.template;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.spy;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class TemplateToolsFallbackTest {

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
    void addTemplate_whenResponseSerializationFails_shouldReturnFallbackSuccess() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());

        DeviceTemplateDto saved = new DeviceTemplateDto();
        saved.setId("tpl_1");
        saved.setName("Lamp");
        when(boardStorageService.addDeviceTemplate(anyLong(), any(DeviceTemplateDto.class))).thenReturn(saved);

        AddTemplateTool tool = new AddTemplateTool(boardStorageService, failingMapper);
        tool.initTolerantMapper();
        String result = tool.execute("""
                {
                  "name":"Lamp",
                  "manifest":{
                    "Modes":["Off","On"],
                    "InitState":"Off"
                  }
                }
                """);
        JsonNode json = objectMapper.readTree(result);

        assertEquals("Template added successfully.", json.path("message").asText());
        assertTrue(json.path("warning").asText().contains("serialization degraded"));
        verify(boardStorageService).addDeviceTemplate(anyLong(), any(DeviceTemplateDto.class));
    }

    @Test
    void deleteTemplate_whenResponseSerializationFails_shouldReturnFallbackSuccess() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());

        DeleteTemplateTool tool = new DeleteTemplateTool(boardStorageService, failingMapper);
        String result = tool.execute("{\"templateId\":\"tpl_1\"}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("Template deleted successfully.", json.path("message").asText());
        assertTrue(json.path("warning").asText().contains("serialization degraded"));
        verify(boardStorageService).deleteDeviceTemplate(1L, "tpl_1");
    }

    @Test
    void addTemplate_invalidJsonArgs_shouldReturnValidationError() throws Exception {
        AddTemplateTool tool = new AddTemplateTool(boardStorageService, objectMapper);
        tool.initTolerantMapper();
        String result = tool.execute("{");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("Invalid JSON arguments.", json.path("error").asText());
        verify(boardStorageService, never()).addDeviceTemplate(anyLong(), any(DeviceTemplateDto.class));
    }

    @Test
    void listTemplates_invalidJsonArgs_shouldReturnValidationError() throws Exception {
        ListTemplatesTool tool = new ListTemplatesTool(boardStorageService, objectMapper);

        String result = tool.execute("{");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("Invalid JSON arguments.", json.path("error").asText());
        verify(boardStorageService, never()).getDeviceTemplates(anyLong());
    }
}
