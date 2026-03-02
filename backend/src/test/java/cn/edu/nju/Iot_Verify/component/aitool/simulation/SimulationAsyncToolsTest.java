package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.aitool.BoardDataHelper;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyBoolean;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class SimulationAsyncToolsTest {

    @Mock
    private BoardDataHelper boardDataHelper;
    @Mock
    private BoardStorageService boardStorageService;
    @Mock
    private SimulationService simulationService;

    private SimulateModelAsyncTool simulateModelAsyncTool;
    private SimulateTaskStatusTool simulateTaskStatusTool;
    private CancelSimulateTaskTool cancelSimulateTaskTool;

    @BeforeEach
    void setUp() {
        ObjectMapper objectMapper = new ObjectMapper();
        simulateModelAsyncTool = new SimulateModelAsyncTool(boardDataHelper, boardStorageService, simulationService, objectMapper);
        simulateTaskStatusTool = new SimulateTaskStatusTool(simulationService, objectMapper);
        cancelSimulateTaskTool = new CancelSimulateTaskTool(simulationService, objectMapper);
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void simulateModelAsync_withoutDevices_shouldFailFast() {
        when(boardDataHelper.getDevicesForVerification(1L)).thenReturn(List.of());

        String result = simulateModelAsyncTool.execute("{}");

        assertTrue(result.contains("No devices found"));
        verify(simulationService, never()).createTask(anyLong(), anyInt());
    }

    @Test
    void simulateModelAsync_withValidInput_shouldStartTask() {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");

        when(boardDataHelper.getDevicesForVerification(1L)).thenReturn(List.of(device));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(simulationService.createTask(1L, 10)).thenReturn(200L);

        String result = simulateModelAsyncTool.execute("{}");

        assertTrue(result.contains("taskId"));
        verify(simulationService).simulateAsync(anyLong(), anyLong(), any(), any(), anyInt(), anyBoolean(), anyInt(), anyBoolean());
    }

    @Test
    void simulateTaskStatus_missingTaskId_shouldReturnError() {
        String result = simulateTaskStatusTool.execute("{}");
        assertTrue(result.contains("taskId"));
    }

    @Test
    void cancelSimulateTask_invalidTaskId_shouldReturnError() {
        String result = cancelSimulateTaskTool.execute("{\"taskId\":-1}");
        assertTrue(result.contains("must be positive"));
    }
}
