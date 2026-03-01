package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.component.aitool.BoardDataHelper;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
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

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyBoolean;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.spy;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class VerificationSyncToolTest {

    @Mock
    private BoardDataHelper boardDataHelper;
    @Mock
    private BoardStorageService boardStorageService;
    @Mock
    private VerificationService verificationService;

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
    void verifyModel_whenResponseSerializationFails_shouldReturnFallbackSuccess() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());

        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");
        when(boardDataHelper.getDevicesForVerification(1L)).thenReturn(List.of(device));
        when(boardStorageService.getRules(1L)).thenReturn(List.of());

        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        when(boardStorageService.getSpecs(1L)).thenReturn(List.of(spec));

        VerificationResultDto result = VerificationResultDto.builder()
                .safe(true)
                .specResults(List.of(true))
                .traces(List.of())
                .checkLogs(List.of("ok"))
                .build();
        when(verificationService.verify(anyLong(), any(), any(), any(), anyBoolean(), anyInt(), anyBoolean()))
                .thenReturn(result);

        VerifyModelTool tool = new VerifyModelTool(boardDataHelper, boardStorageService, verificationService, failingMapper);
        String response = tool.execute("{}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("Verification completed.", json.path("message").asText());
        assertTrue(json.path("warning").asText().contains("serialization degraded"));
        verify(verificationService).verify(anyLong(), any(), any(), any(), anyBoolean(), anyInt(), anyBoolean());
    }
}
