package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.SimulationService;
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
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class SimulationAsyncToolsTest {

    @Mock
    private BoardDataConverter boardDataConverter;
    @Mock
    private BoardStorageService boardStorageService;
    @Mock
    private SimulationService simulationService;

    private ObjectMapper objectMapper;
    private SimulateModelAsyncTool simulateModelAsyncTool;
    private SimulateTaskStatusTool simulateTaskStatusTool;
    private CancelSimulateTaskTool cancelSimulateTaskTool;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        simulateModelAsyncTool = new SimulateModelAsyncTool(boardDataConverter, boardStorageService, simulationService, objectMapper);
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
        when(boardDataConverter.getDevicesForVerification(1L)).thenReturn(List.of());

        String result = simulateModelAsyncTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertTrue(result.contains("No devices found"));
        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        verify(simulationService, never()).createTask(anyLong(), anyInt());
    }

    @Test
    void simulateModelAsync_withValidInput_shouldStartTask() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");

        when(boardDataConverter.getDevicesForVerification(1L)).thenReturn(List.of(device));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(simulationService.createTask(1L, 10)).thenReturn(200L);

        String result = simulateModelAsyncTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertTrue(result.contains("taskId"));
        assertEquals("PENDING", json.path("taskStatus").asText());
        verify(simulationService).simulateAsync(anyLong(), anyLong(), any());
    }

    @Test
    void simulateModelAsync_whenQueueRejected_shouldReturnStructuredServiceUnavailable() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");

        when(boardDataConverter.getDevicesForVerification(1L)).thenReturn(List.of(device));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(simulationService.createTask(1L, 10)).thenReturn(201L);
        doThrow(new TaskRejectedException("busy")).when(simulationService)
                .simulateAsync(anyLong(), anyLong(), any());

        String result = simulateModelAsyncTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("SERVICE_UNAVAILABLE", json.path("errorCode").asText());
        assertEquals(503, json.path("status").asInt());
        verify(simulationService).failTaskById(201L, "Server busy, please try again later");
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
    void cancelSimulateTask_whenResponseSerializationFails_shouldReturnFallbackSuccess() throws Exception {
        ObjectMapper failingMapper = mock(ObjectMapper.class);
        when(failingMapper.readTree(anyString())).thenReturn(new ObjectMapper().readTree("{\"taskId\":7}"));
        when(failingMapper.writeValueAsString(any())).thenThrow(new RuntimeException("boom"));
        when(simulationService.cancelTask(1L, 7L)).thenReturn(true);

        CancelSimulateTaskTool fallbackTool = new CancelSimulateTaskTool(simulationService, failingMapper);
        String result = fallbackTool.execute("{\"taskId\":7}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("Simulation task cancellation completed.", json.path("message").asText());
        assertTrue(json.path("warning").asText().contains("serialization degraded"));
    }
}
