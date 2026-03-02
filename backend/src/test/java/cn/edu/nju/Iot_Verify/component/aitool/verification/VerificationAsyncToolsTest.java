package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.aitool.BoardDataHelper;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import cn.edu.nju.Iot_Verify.service.VerificationService;
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
class VerificationAsyncToolsTest {

    @Mock
    private BoardDataHelper boardDataHelper;
    @Mock
    private BoardStorageService boardStorageService;
    @Mock
    private VerificationService verificationService;

    private VerifyModelAsyncTool verifyModelAsyncTool;
    private VerifyTaskStatusTool verifyTaskStatusTool;
    private CancelVerifyTaskTool cancelVerifyTaskTool;

    @BeforeEach
    void setUp() {
        ObjectMapper objectMapper = new ObjectMapper();
        verifyModelAsyncTool = new VerifyModelAsyncTool(boardDataHelper, boardStorageService, verificationService, objectMapper);
        verifyTaskStatusTool = new VerifyTaskStatusTool(verificationService, objectMapper);
        cancelVerifyTaskTool = new CancelVerifyTaskTool(verificationService, objectMapper);
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void verifyModelAsync_withoutDevices_shouldFailFast() {
        when(boardDataHelper.getDevicesForVerification(1L)).thenReturn(List.of());

        String result = verifyModelAsyncTool.execute("{}");

        assertTrue(result.contains("No devices found"));
        verify(verificationService, never()).createTask(anyLong());
    }

    @Test
    void verifyModelAsync_withValidInput_shouldStartTask() {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");

        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");

        when(boardDataHelper.getDevicesForVerification(1L)).thenReturn(List.of(device));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of(spec));
        when(verificationService.createTask(1L)).thenReturn(100L);

        String result = verifyModelAsyncTool.execute("{}");

        assertTrue(result.contains("taskId"));
        verify(verificationService).verifyAsync(anyLong(), anyLong(), any(), any(), any(), anyBoolean(), anyInt(), anyBoolean());
    }

    @Test
    void verifyTaskStatus_missingTaskId_shouldReturnError() {
        String result = verifyTaskStatusTool.execute("{}");
        assertTrue(result.contains("taskId"));
    }

    @Test
    void cancelVerifyTask_invalidTaskId_shouldReturnError() {
        String result = cancelVerifyTaskTool.execute("{\"taskId\":0}");
        assertTrue(result.contains("must be positive"));
    }
}
