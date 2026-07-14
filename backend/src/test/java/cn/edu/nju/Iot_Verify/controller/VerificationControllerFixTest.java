package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.component.model.ModelRequestParser;
import cn.edu.nju.Iot_Verify.dto.fix.FixRequestDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixApplyRequestDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixApplyResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRangeSelection;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.service.FixService;
import cn.edu.nju.Iot_Verify.service.VerificationService;
import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class VerificationControllerFixTest {

    @Mock private VerificationService verificationService;
    @Mock private FixService fixService;
    @Mock private ModelRequestParser modelRequestParser;

    private VerificationController controller;
    private Validator validator;

    @BeforeEach
    void setUp() {
        controller = new VerificationController(verificationService, fixService, modelRequestParser);
        validator = Validation.buildDefaultValidatorFactory().getValidator();
        lenient().when(fixService.fix(anyLong(), anyLong(), any(), any()))
                .thenReturn(FixResultDto.builder().fixable(false).build());
    }

    @SuppressWarnings("unchecked")
    private List<String> captureStrategies() {
        ArgumentCaptor<List<String>> captor = ArgumentCaptor.forClass(List.class);
        verify(fixService).fix(anyLong(), anyLong(), captor.capture(), any());
        return captor.getValue();
    }

    @SuppressWarnings("unchecked")
    private Map<String, PreferredRange> capturePreferredRanges() {
        ArgumentCaptor<Map<String, PreferredRange>> captor = ArgumentCaptor.forClass(Map.class);
        verify(fixService).fix(anyLong(), anyLong(), any(), captor.capture());
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
    void fix_emptyStrategiesList_isRejectedByRequestContract() {
        FixRequestDto request = new FixRequestDto();
        request.setStrategies(List.of());

        assertFalse(validator.validate(request).isEmpty());
        verifyNoInteractions(fixService);
    }

    @Test
    void fix_duplicateStrategies_areRejectedByRequestContract() {
        FixRequestDto request = new FixRequestDto();
        request.setStrategies(List.of("parameter", "parameter"));

        assertFalse(validator.validate(request).isEmpty());
    }

    @Test
    void applyFix_unknownStrategy_isRejectedByRequestContract() {
        FixApplyRequestDto request = new FixApplyRequestDto();
        request.setStrategy("disable");

        assertFalse(validator.validate(request).isEmpty());
    }

    @Test
    void fix_explicitStrategies_passesThrough() {
        FixRequestDto request = new FixRequestDto();
        request.setStrategies(List.of("remove"));
        controller.fix(1L, 1L, request);
        assertEquals(List.of("remove"), captureStrategies());
    }

    @Test
    void fix_preferredRangeSelections_keepTargetIdMap() {
        String targetId = PreferredRangeSelection.targetIdFor(0, 1);
        FixRequestDto request = new FixRequestDto();
        request.setPreferredRangeSelections(List.of(PreferredRangeSelection.builder()
                .targetId(targetId)
                .lower(10)
                .upper(20)
                .build()));

        controller.fix(1L, 1L, request);

        Map<String, PreferredRange> ranges = capturePreferredRanges();
        assertNotNull(ranges);
        assertEquals(10, ranges.get(targetId).getLower());
        assertEquals(20, ranges.get(targetId).getUpper());
    }

    @Test
    void applyFix_forwardsOnlyStrategyAndPreferredRanges() {
        String targetId = PreferredRangeSelection.targetIdFor(1L, 0, 0);
        FixApplyRequestDto request = new FixApplyRequestDto();
        request.setStrategy("parameter");
        request.setPreferredRangeSelections(List.of(PreferredRangeSelection.builder()
                .targetId(targetId)
                .lower(10)
                .upper(20)
                .build()));
        when(fixService.applyFix(eq(1L), eq(2L), eq("parameter"), any()))
                .thenReturn(FixApplyResultDto.builder().applied(true).build());

        controller.applyFix(1L, 2L, request);

        @SuppressWarnings("unchecked")
        ArgumentCaptor<Map<String, PreferredRange>> ranges = ArgumentCaptor.forClass(Map.class);
        verify(fixService).applyFix(eq(1L), eq(2L), eq("parameter"), ranges.capture());
        assertEquals(10, ranges.getValue().get(targetId).getLower());
        assertEquals(20, ranges.getValue().get(targetId).getUpper());
    }
}
