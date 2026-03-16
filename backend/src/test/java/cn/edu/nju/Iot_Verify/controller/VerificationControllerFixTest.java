package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.fix.FixRequestDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.service.FixService;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class VerificationControllerFixTest {

    @Mock private VerificationService verificationService;
    @Mock private FixService fixService;

    private VerificationController controller;

    @BeforeEach
    void setUp() {
        controller = new VerificationController(verificationService, fixService);
        lenient().when(fixService.fix(anyLong(), anyLong(), any(), any()))
                .thenReturn(FixResultDto.builder().fixable(false).build());
    }

    @SuppressWarnings("unchecked")
    private List<String> captureStrategies() {
        ArgumentCaptor<List<String>> captor = ArgumentCaptor.forClass(List.class);
        verify(fixService).fix(anyLong(), anyLong(), captor.capture(), any());
        return captor.getValue();
    }

    @Test
    void fix_nullBody_passesNullStrategies() {
        controller.fix(1L, 1L, null);
        assertNull(captureStrategies());
    }

    @Test
    void fix_emptyRequest_passesNullStrategies() {
        FixRequestDto request = new FixRequestDto();
        controller.fix(1L, 1L, request);
        assertNull(captureStrategies());
    }

    @Test
    void fix_emptyStrategiesList_passesEmptyList() {
        FixRequestDto request = new FixRequestDto();
        request.setStrategies(List.of());
        controller.fix(1L, 1L, request);
        assertEquals(List.of(), captureStrategies());
    }

    @Test
    void fix_explicitStrategies_passesThrough() {
        FixRequestDto request = new FixRequestDto();
        request.setStrategies(List.of("disable"));
        controller.fix(1L, 1L, request);
        assertEquals(List.of("disable"), captureStrategies());
    }
}
