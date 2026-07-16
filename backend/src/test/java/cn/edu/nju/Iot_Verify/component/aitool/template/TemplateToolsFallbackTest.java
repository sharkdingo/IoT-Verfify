package cn.edu.nju.Iot_Verify.component.aitool.template;

import cn.edu.nju.Iot_Verify.component.aitool.AiDestructiveActionGuard;
import cn.edu.nju.Iot_Verify.component.template.DeviceTemplateSchemaValidator;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDeletionResultDto;
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
import static org.mockito.Mockito.verifyNoInteractions;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class TemplateToolsFallbackTest {

    @Mock
    private BoardStorageService boardStorageService;
    @Mock
    private DeviceTemplateSchemaValidator deviceTemplateSchemaValidator;

    private ObjectMapper objectMapper;
    private AiDestructiveActionGuard destructiveActionGuard;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        destructiveActionGuard = new AiDestructiveActionGuard(objectMapper);
        UserContextHolder.setUserId(1L);
        UserContextHolder.setChatSessionId("template-test-session");
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void listTemplates_rejectsUnknownOptionBeforeReadingCatalog() throws Exception {
        ListTemplatesTool tool = new ListTemplatesTool(boardStorageService, objectMapper);

        JsonNode json = objectMapper.readTree(tool.execute("{\"details\":true}"));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        verify(boardStorageService, never()).getDeviceTemplates(1L);
    }

    @Test
    void addTemplate_whenResponseSerializationFails_shouldReturnFallbackSuccess() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());

        DeviceTemplateDto saved = new DeviceTemplateDto();
        saved.setId(1L);
        saved.setName("Lamp");
        when(boardStorageService.addDeviceTemplate(anyLong(), any(DeviceTemplateDto.class))).thenReturn(saved);

        AddTemplateTool tool = new AddTemplateTool(boardStorageService, failingMapper, deviceTemplateSchemaValidator);
        tool.initTolerantMapper();
        String result = tool.execute("""
                {
                  "name":"Lamp",
                  "manifest":{
                    "Modes":["LampState"],
                    "InitState":"Off",
                    "WorkingStates":[{"Name":"Off"},{"Name":"On"}]
                  }
                }
                """);
        JsonNode json = objectMapper.readTree(result);

        assertEquals("RESULT_UNAVAILABLE", json.path("resultStatus").asText());
        assertTrue(json.path("mutationMayHaveCommitted").asBoolean());
        assertTrue(json.path("warning").asText().contains("serialization failed"));
        verify(boardStorageService).addDeviceTemplate(anyLong(), any(DeviceTemplateDto.class));
    }

    @Test
    void deleteTemplate_whenResponseSerializationFails_shouldReturnFallbackSuccess() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());
        DeviceTemplateDto deleted = new DeviceTemplateDto();
        deleted.setId(42L);
        deleted.setName("Lamp");
        DeviceTemplateDeletionResultDto deletion = DeviceTemplateDeletionResultDto.builder()
                .operation("deleted").impactToken("token-42").canDelete(true)
                .template(deleted).deletedTemplate(deleted).currentTemplates(java.util.List.of()).build();
        DeviceTemplateDeletionResultDto preview = DeviceTemplateDeletionResultDto.builder()
                .operation("preview").impactToken("token-42").canDelete(true)
                .template(deleted).currentTemplates(java.util.List.of(deleted)).build();
        when(boardStorageService.previewDeviceTemplateDeletion(1L, 42L)).thenReturn(preview);
        when(boardStorageService.deleteDeviceTemplate(1L, 42L, "token-42")).thenReturn(deletion);

        DeleteTemplateTool previewTool = new DeleteTemplateTool(
                boardStorageService, objectMapper, destructiveActionGuard);
        JsonNode previewJson = objectMapper.readTree(
                previewTool.execute("{\"templateId\":42,\"confirmed\":false}"));
        UserContextHolder.setDestructiveActionConfirmed(true);

        DeleteTemplateTool tool = new DeleteTemplateTool(boardStorageService, failingMapper, destructiveActionGuard);
        String result = tool.execute("{\"templateId\":42,\"confirmed\":true,\"impactToken\":\""
                + previewJson.path("preview").path("impactToken").asText() + "\"}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("RESULT_UNAVAILABLE", json.path("resultStatus").asText());
        assertTrue(json.path("mutationMayHaveCommitted").asBoolean());
        assertTrue(json.path("warning").asText().contains("serialization failed"));
        verify(boardStorageService).deleteDeviceTemplate(1L, 42L, "token-42");
    }

    @Test
    void deleteTemplate_withoutExplicitConfirmation_shouldReturnPreviewWithoutMutation() throws Exception {
        DeviceTemplateDto target = new DeviceTemplateDto();
        target.setId(42L);
        target.setName("Lamp");
        when(boardStorageService.previewDeviceTemplateDeletion(1L, 42L)).thenReturn(
                DeviceTemplateDeletionResultDto.builder()
                        .operation("preview").impactToken("token-42").canDelete(true)
                        .template(target).currentTemplates(java.util.List.of(target)).build());

        DeleteTemplateTool tool = new DeleteTemplateTool(boardStorageService, objectMapper, destructiveActionGuard);
        String result = tool.execute("{\"templateId\":42,\"confirmed\":true}");
        JsonNode json = objectMapper.readTree(result);

        assertTrue(json.path("requiresUserConfirmation").asBoolean());
        assertEquals("preview", json.path("preview").path("operation").asText());
        assertEquals(false, json.path("mutationMayHaveCommitted").asBoolean(false));
        verify(boardStorageService, never()).deleteDeviceTemplate(anyLong(), anyLong(), any());
    }

    @Test
    void deleteTemplate_stalePreview_returnsCurrentStructuredPreview() throws Exception {
        DeviceTemplateDto target = new DeviceTemplateDto();
        target.setId(42L);
        target.setName("Lamp");
        DeviceTemplateDeletionResultDto originalPreview = DeviceTemplateDeletionResultDto.builder()
                .operation("preview").impactToken("old-token").canDelete(true)
                .template(target).currentTemplates(java.util.List.of(target)).build();
        DeviceTemplateDeletionResultDto currentPreview = DeviceTemplateDeletionResultDto.builder()
                .operation("preview").impactToken("new-token").canDelete(true)
                .template(target).currentTemplates(java.util.List.of()).build();
        when(boardStorageService.previewDeviceTemplateDeletion(1L, 42L))
                .thenReturn(originalPreview, currentPreview);

        DeleteTemplateTool tool = new DeleteTemplateTool(boardStorageService, objectMapper, destructiveActionGuard);
        JsonNode original = objectMapper.readTree(
                tool.execute("{\"templateId\":42,\"confirmed\":false}"));
        UserContextHolder.setDestructiveActionConfirmed(true);

        JsonNode json = objectMapper.readTree(tool.execute(
                "{\"templateId\":42,\"confirmed\":true,\"impactToken\":\""
                        + original.path("preview").path("impactToken").asText() + "\"}"));

        assertEquals(409, json.path("status").asInt());
        assertEquals("CONFIRMATION_STALE", json.path("errorCode").asText());
        assertEquals("preview", json.path("currentPreview").path("operation").asText());
        assertTrue(json.path("currentPreview").path("impactToken").asText().length() > 20);
        verify(boardStorageService, never()).deleteDeviceTemplate(anyLong(), anyLong(), any());
    }

    @Test
    void addTemplate_invalidJsonArgs_shouldReturnValidationError() throws Exception {
        AddTemplateTool tool = new AddTemplateTool(boardStorageService, objectMapper, deviceTemplateSchemaValidator);
        tool.initTolerantMapper();
        String result = tool.execute("{");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("Invalid JSON arguments.", json.path("error").asText());
        verify(boardStorageService, never()).addDeviceTemplate(anyLong(), any(DeviceTemplateDto.class));
    }

    @Test
    void templateMutationsRejectWrongTypesAndUnknownFieldsBeforeStorage() throws Exception {
        AddTemplateTool addTool = new AddTemplateTool(
                boardStorageService, objectMapper, deviceTemplateSchemaValidator);
        addTool.initTolerantMapper();
        DeleteTemplateTool deleteTool = new DeleteTemplateTool(boardStorageService, objectMapper, destructiveActionGuard);

        JsonNode numericName = objectMapper.readTree(
                addTool.execute("{\"name\":7,\"manifest\":{}}"));
        JsonNode unknownDeleteField = objectMapper.readTree(
                deleteTool.execute("{\"templateId\":7,\"confirmed\":false,\"name\":\"Lamp\"}"));

        assertEquals("VALIDATION_ERROR", numericName.path("errorCode").asText());
        assertTrue(numericName.path("error").asText().contains("non-empty string"));
        assertEquals("VALIDATION_ERROR", unknownDeleteField.path("errorCode").asText());
        assertTrue(unknownDeleteField.path("error").asText().contains("name"));
        verifyNoInteractions(boardStorageService);
    }

    @Test
    void deleteTemplate_outOfRangeLong_shouldReturn400() throws Exception {
        DeleteTemplateTool tool = new DeleteTemplateTool(boardStorageService, objectMapper, destructiveActionGuard);
        String result = tool.execute("{\"templateId\":99999999999999999999}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertTrue(json.path("error").asText().contains("out of range"));
        verify(boardStorageService, never()).deleteDeviceTemplate(anyLong(), anyLong(), any());
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
