package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationTaskDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;
import java.util.Map;
import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.spy;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.verifyNoMoreInteractions;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class VerificationAsyncToolsTest {

    @Mock
    private BoardDataConverter boardDataConverter;
    @Mock
    private VerificationService verificationService;

    private ObjectMapper objectMapper;
    private VerifyModelAsyncTool verifyModelAsyncTool;
    private VerifyTaskStatusTool verifyTaskStatusTool;
    private CancelVerifyTaskTool cancelVerifyTaskTool;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper().findAndRegisterModules();
        verifyModelAsyncTool = new VerifyModelAsyncTool(boardDataConverter, verificationService, objectMapper);
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
        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(emptySnapshot());

        String result = verifyModelAsyncTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertTrue(result.contains("No devices found"));
        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        verify(verificationService, never()).submitVerificationWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void verifyModelAsync_invalidIntensity_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        String result = verifyModelAsyncTool.execute("{\"attackBudget\":-1}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("attackBudget must be between 0 and 50.", json.path("error").asText());
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(verificationService, never()).submitVerificationWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void verifyModelAsync_attackEnabledWithZeroBudget_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        String result = verifyModelAsyncTool.execute(
                "{\"attackMode\":\"exhaustive\",\"attackBudget\":0}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("attackBudget must be between 1 and 50.", json.path("error").asText());
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(verificationService, never()).submitVerificationWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void verifyModelAsync_withValidInput_shouldStartTask() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");

        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");

        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(snapshot(device, spec));
        when(verificationService.submitVerificationWithTemplateSnapshot(eq(1L), any(), any()))
                .thenReturn(100L);
        when(verificationService.getTask(1L, 100L)).thenReturn(VerificationTaskDto.builder()
                .id(100L)
                .status("PENDING")
                .progress(0)
                .isAttack(false)
                .attackBudget(0)
                .enablePrivacy(false)
                .modelSnapshot(ModelRunSnapshotDto.captured(
                        LocalDateTime.of(2026, 7, 12, 9, 30), 1, 0, 1, 0, 1))
                .build());

        String result = verifyModelAsyncTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertTrue(result.contains("taskId"));
        assertEquals("PENDING", json.path("taskStatus").asText());
        assertEquals(0, json.path("progress").asInt());
        assertEquals(false, json.path("isAttack").asBoolean());
        assertEquals(0, json.path("attackBudget").asInt());
        assertEquals(false, json.path("enablePrivacy").asBoolean());
        assertEquals(1, json.path("modelSnapshot").path("deviceCount").asInt());
        assertTrue(json.path("modelSnapshot").path("templatesFrozen").asBoolean());
        assertTrue(json.path("message").asText().contains("completion is not implied"));
        verify(verificationService).submitVerificationWithTemplateSnapshot(eq(1L), any(), any());
        verify(verificationService).getTask(1L, 100L);
    }

    @Test
    void verifyModelAsync_whenQueueRejected_shouldReturnStructuredServiceUnavailable() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");

        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");

        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(snapshot(device, spec));
        doThrow(new ServiceUnavailableException("Server busy, please try again later")).when(verificationService)
                .submitVerificationWithTemplateSnapshot(eq(1L), any(), any());

        String result = verifyModelAsyncTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("SERVICE_UNAVAILABLE", json.path("errorCode").asText());
        assertEquals(503, json.path("status").asInt());
        // The captured-snapshot submit path owns task creation and failure compensation internally,
        // so the AI tool only invokes the high-level submit entry point.
        verify(verificationService).submitVerificationWithTemplateSnapshot(eq(1L), any(), any());
        verifyNoMoreInteractions(verificationService);
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
    void taskTools_rejectUnknownFieldsBeforeCallingService() throws Exception {
        JsonNode status = objectMapper.readTree(verifyTaskStatusTool.execute(
                "{\"taskId\":12,\"taksId\":12}"));
        JsonNode cancel = objectMapper.readTree(cancelVerifyTaskTool.execute(
                "{\"taskId\":12,\"force\":true}"));

        assertEquals("VALIDATION_ERROR", status.path("errorCode").asText());
        assertEquals("VALIDATION_ERROR", cancel.path("errorCode").asText());
        verify(verificationService, never()).getTask(anyLong(), anyLong());
        verify(verificationService, never()).cancelTask(anyLong(), anyLong());
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
    void cancelVerifyTask_whenResponseSerializationFails_shouldReturnAmbiguousMutationResult() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());
        when(verificationService.cancelTask(1L, 7L)).thenReturn(
                cn.edu.nju.Iot_Verify.dto.model.TaskCancellationResultDto.builder()
                        .taskId(7L)
                        .cancellationAccepted(true)
                        .cancellationOutcome(cn.edu.nju.Iot_Verify.dto.model.TaskCancellationOutcome.ACCEPTED)
                        .taskStatus("CANCELLED")
                        .executionMayStillBeStopping(true)
                        .build());

        CancelVerifyTaskTool fallbackTool = new CancelVerifyTaskTool(verificationService, failingMapper);
        String result = fallbackTool.execute("{\"taskId\":7}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("RESULT_UNAVAILABLE", json.path("resultStatus").asText());
        assertEquals(false, json.path("resultAvailable").asBoolean());
        assertTrue(json.path("mutationMayHaveCommitted").asBoolean());
        assertTrue(json.path("message").asText().contains("refresh current state"));
        assertTrue(json.path("warning").asText().contains("serialization failed"));
    }

    private ModelInputSnapshot emptySnapshot() {
        return new ModelInputSnapshot(List.of(), List.of(), List.of(), List.of(), List.of(), Map.of());
    }

    private ModelInputSnapshot snapshot(DeviceVerificationDto device, SpecificationDto spec) {
        return new ModelInputSnapshot(
                List.of(), List.of(device), List.of(), List.of(), List.of(spec), Map.of());
    }
}
