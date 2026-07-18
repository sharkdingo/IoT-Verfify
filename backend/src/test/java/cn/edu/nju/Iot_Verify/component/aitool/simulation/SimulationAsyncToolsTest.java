package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTaskDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;
import java.time.LocalDateTime;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.verifyNoMoreInteractions;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class SimulationAsyncToolsTest {

    @Mock
    private BoardDataConverter boardDataConverter;
    @Mock
    private SimulationService simulationService;

    private ObjectMapper objectMapper;
    private SimulateModelAsyncTool simulateModelAsyncTool;
    private SimulateTaskStatusTool simulateTaskStatusTool;
    private CancelSimulateTaskTool cancelSimulateTaskTool;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper().findAndRegisterModules();
        simulateModelAsyncTool = new SimulateModelAsyncTool(boardDataConverter, simulationService, objectMapper);
        simulateTaskStatusTool = new SimulateTaskStatusTool(simulationService, objectMapper);
        cancelSimulateTaskTool = new CancelSimulateTaskTool(simulationService, objectMapper);
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void simulateModelAsync_withoutDevices_shouldFailFast() throws Exception {
        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(emptySnapshot());

        String result = simulateModelAsyncTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertTrue(result.contains("No devices found"));
        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        verify(simulationService, never()).submitSimulationWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void simulateModelAsync_invalidSteps_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        String result = simulateModelAsyncTool.execute("{\"steps\":0}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("steps must be between 1 and 100.", json.path("error").asText());
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(simulationService, never()).submitSimulationWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void simulateModelAsync_exactModeWithoutPoints_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        String result = simulateModelAsyncTool.execute(
                "{\"attackMode\":\"exact\",\"attackPoints\":[]}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("attackPoints must contain between 1 and 50 points when attackMode is exact.",
                json.path("error").asText());
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(simulationService, never()).submitSimulationWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void simulateModelAsync_exhaustiveMode_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        String result = simulateModelAsyncTool.execute("{\"attackMode\":\"exhaustive\"}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertTrue(json.path("error").asText().contains("attackMode must be one of"));
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(simulationService, never()).submitSimulationWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void simulateModelAsync_withValidInput_shouldStartTask() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");

        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(snapshot(device));
        when(simulationService.submitSimulationWithTemplateSnapshot(eq(1L), any(), any()))
                .thenReturn(200L);
        when(simulationService.getTask(1L, 200L)).thenReturn(SimulationTaskDto.builder()
                .id(200L)
                .status("PENDING")
                .progress(0)
                .requestedSteps(10)
                .isAttack(false)
                .attackBudget(0)
                .enablePrivacy(false)
                .modelSnapshot(ModelRunSnapshotDto.captured(
                        LocalDateTime.of(2026, 7, 12, 9, 30), 1, 0, 0, 0, 1))
                .build());

        String result = simulateModelAsyncTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertTrue(result.contains("taskId"));
        assertEquals("PENDING", json.path("taskStatus").asText());
        assertEquals(10, json.path("requestedSteps").asInt());
        assertEquals(false, json.path("isAttack").asBoolean());
        assertEquals(0, json.path("attackBudget").asInt());
        assertEquals(false, json.path("enablePrivacy").asBoolean());
        assertEquals(1, json.path("modelSnapshot").path("deviceCount").asInt());
        assertTrue(json.path("modelSnapshot").path("templatesFrozen").asBoolean());
        assertTrue(json.path("message").asText().contains("completion is not implied"));
        verify(simulationService).submitSimulationWithTemplateSnapshot(eq(1L), any(), any());
        verify(simulationService).getTask(1L, 200L);
    }

    @Test
    void simulateModelAsync_whenQueueRejected_shouldReturnStructuredServiceUnavailable() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");

        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(snapshot(device));
        doThrow(new ServiceUnavailableException("Server busy, please try again later")).when(simulationService)
                .submitSimulationWithTemplateSnapshot(eq(1L), any(), any());

        String result = simulateModelAsyncTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("SERVICE_UNAVAILABLE", json.path("errorCode").asText());
        assertEquals(503, json.path("status").asInt());
        // The captured-snapshot submit path owns task creation and failure compensation internally,
        // so the AI tool only invokes the high-level submit entry point.
        verify(simulationService).submitSimulationWithTemplateSnapshot(eq(1L), any(), any());
        verifyNoMoreInteractions(simulationService);
    }

    @Test
    void simulateTaskStatus_missingTaskId_shouldReturnError() throws Exception {
        String result = simulateTaskStatusTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);
        assertTrue(result.contains("taskId"));
        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
    }

    @Test
    void taskTools_rejectUnknownFieldsBeforeCallingService() throws Exception {
        JsonNode status = objectMapper.readTree(simulateTaskStatusTool.execute(
                "{\"taskId\":12,\"taksId\":12}"));
        JsonNode cancel = objectMapper.readTree(cancelSimulateTaskTool.execute(
                "{\"taskId\":12,\"force\":true}"));

        assertEquals("VALIDATION_ERROR", status.path("errorCode").asText());
        assertEquals("VALIDATION_ERROR", cancel.path("errorCode").asText());
        verify(simulationService, never()).getTask(anyLong(), anyLong());
        verify(simulationService, never()).cancelTask(anyLong(), anyLong());
    }

    @Test
    void simulateTaskStatus_whenServiceThrowsBaseException_shouldReturnStructuredBusinessError() throws Exception {
        when(simulationService.getTask(1L, 9L)).thenThrow(new BadRequestException("invalid simulation task"));

        String result = simulateTaskStatusTool.execute("{\"taskId\":9}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("BUSINESS_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("invalid simulation task", json.path("error").asText());
    }

    @Test
    void cancelSimulateTask_invalidTaskId_shouldReturnError() throws Exception {
        String result = cancelSimulateTaskTool.execute("{\"taskId\":-1}");
        JsonNode json = objectMapper.readTree(result);
        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertTrue(result.contains("must be positive"));
    }

    @Test
    void cancelSimulateTask_whenResponseSerializationFails_shouldReturnAmbiguousMutationResult() throws Exception {
        ObjectMapper failingMapper = mock(ObjectMapper.class);
        when(failingMapper.readTree(anyString())).thenReturn(new ObjectMapper().readTree("{\"taskId\":7}"));
        when(failingMapper.writeValueAsString(any())).thenThrow(new RuntimeException("boom"));
        when(simulationService.cancelTask(1L, 7L)).thenReturn(
                cn.edu.nju.Iot_Verify.dto.model.TaskCancellationResultDto.builder()
                        .taskId(7L)
                        .cancellationAccepted(true)
                        .cancellationOutcome(cn.edu.nju.Iot_Verify.dto.model.TaskCancellationOutcome.ACCEPTED)
                        .taskStatus("CANCELLED")
                        .executionMayStillBeStopping(true)
                        .build());

        CancelSimulateTaskTool fallbackTool = new CancelSimulateTaskTool(simulationService, failingMapper);
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

    private ModelInputSnapshot snapshot(DeviceVerificationDto device) {
        return new ModelInputSnapshot(
                List.of(), List.of(device), List.of(), List.of(), List.of(), Map.of());
    }
}
