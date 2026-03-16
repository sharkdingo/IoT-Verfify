package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.core.task.TaskRejectedException;

import java.util.List;

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
class VerificationAsyncToolsTest {

    @Mock
    private BoardDataConverter boardDataConverter;
    @Mock
    private BoardStorageService boardStorageService;
    @Mock
    private VerificationService verificationService;

    private ObjectMapper objectMapper;
    private VerifyModelAsyncTool verifyModelAsyncTool;
    private VerifyTaskStatusTool verifyTaskStatusTool;
    private CancelVerifyTaskTool cancelVerifyTaskTool;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        verifyModelAsyncTool = new VerifyModelAsyncTool(boardDataConverter, boardStorageService, verificationService, objectMapper);
        verifyTaskStatusTool = new VerifyTaskStatusTool(verificationService, objectMapper);
        cancelVerifyTaskTool = new CancelVerifyTaskTool(verificationService, objectMapper);
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void verifyModelAsync_withoutDevices_shouldFailFast() throws Exception {
        when(boardDataConverter.getDevicesForVerification(1L)).thenReturn(List.of());

        String result = verifyModelAsyncTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertTrue(result.contains("No devices found"));
        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        verify(verificationService, never()).createTask(anyLong());
    }

    @Test
    void verifyModelAsync_withValidInput_shouldStartTask() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");

        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");

        when(boardDataConverter.getDevicesForVerification(1L)).thenReturn(List.of(device));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of(spec));
        when(verificationService.createTask(1L)).thenReturn(100L);

        String result = verifyModelAsyncTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertTrue(result.contains("taskId"));
        assertEquals("PENDING", json.path("taskStatus").asText());
        verify(verificationService).verifyAsync(anyLong(), anyLong(), any());
    }

    @Test
    void verifyModelAsync_whenQueueRejected_shouldReturnStructuredServiceUnavailable() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");

        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");

        when(boardDataConverter.getDevicesForVerification(1L)).thenReturn(List.of(device));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of(spec));
        when(verificationService.createTask(1L)).thenReturn(101L);
        doThrow(new TaskRejectedException("busy")).when(verificationService)
                .verifyAsync(anyLong(), anyLong(), any());

        String result = verifyModelAsyncTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("SERVICE_UNAVAILABLE", json.path("errorCode").asText());
        assertEquals(503, json.path("status").asInt());
        verify(verificationService).failTaskById(101L, "Server busy, please try again later");
    }

    @Test
    void verifyTaskStatus_missingTaskId_shouldReturnError() throws Exception {
        String result = verifyTaskStatusTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);
        assertTrue(result.contains("taskId"));
        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
    }

    @Test
    void verifyTaskStatus_whenServiceThrowsBaseException_shouldReturnStructuredBusinessError() throws Exception {
        when(verificationService.getTask(1L, 12L)).thenThrow(new BadRequestException("invalid task"));

        String result = verifyTaskStatusTool.execute("{\"taskId\":12}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("BUSINESS_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("invalid task", json.path("error").asText());
    }

    @Test
    void cancelVerifyTask_invalidTaskId_shouldReturnError() throws Exception {
        String result = cancelVerifyTaskTool.execute("{\"taskId\":0}");
        JsonNode json = objectMapper.readTree(result);
        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertTrue(result.contains("must be positive"));
    }

    @Test
    void cancelVerifyTask_whenResponseSerializationFails_shouldReturnFallbackSuccess() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());
        when(verificationService.cancelTask(1L, 7L)).thenReturn(true);

        CancelVerifyTaskTool fallbackTool = new CancelVerifyTaskTool(verificationService, failingMapper);
        String result = fallbackTool.execute("{\"taskId\":7}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("Verification task cancellation completed.", json.path("message").asText());
        assertTrue(json.path("warning").asText().contains("serialization degraded"));
    }
}
