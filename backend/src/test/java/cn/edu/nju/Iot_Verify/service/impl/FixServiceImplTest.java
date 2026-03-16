package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.fixer.RuleFixer;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRange;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.po.TracePo;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.repository.TraceRepository;
import cn.edu.nju.Iot_Verify.util.mapper.TraceMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.time.LocalDateTime;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class FixServiceImplTest {

    @Mock private TraceRepository traceRepository;
    @Mock private TraceMapper traceMapper;
    @Mock private SmvGenerator smvGenerator;
    @Mock private RuleFixer ruleFixer;
    @Mock private DeviceTemplateRepository deviceTemplateRepository;

    private FixServiceImpl fixService;

    @BeforeEach
    void setUp() {
        FixConfig fixConfig = new FixConfig();
        fixConfig.setMaxAttempts(20);
        fixService = new FixServiceImpl(traceRepository, traceMapper, smvGenerator, ruleFixer, fixConfig, deviceTemplateRepository);
    }

    private void setupTraceContext() {
        TracePo po = new TracePo();
        po.setId(1L);
        po.setUserId(1L);
        po.setRequestJson("{\"devices\":[{\"varName\":\"d1\",\"templateName\":\"t1\"}],"
                + "\"rules\":[],\"specs\":[],\"isAttack\":false,\"intensity\":0,\"enablePrivacy\":false}");
        when(traceRepository.findByIdAndUserId(1L, 1L)).thenReturn(Optional.of(po));

        TraceDto traceDto = new TraceDto();
        traceDto.setViolatedSpecId("s0");
        when(traceMapper.toDto(po)).thenReturn(traceDto);
        when(smvGenerator.buildDeviceSmvMap(anyLong(), anyList())).thenReturn(Map.of());
        when(ruleFixer.fix(anyLong(), any(), any(), anyList(), anyList(), anyList(),
                anyMap(), anyLong(), anyBoolean(), anyInt(), anyBoolean(), any(), anyInt(), any()))
                .thenReturn(FixResultDto.builder().fixable(false).build());
    }

    // ---- P0: strategies passthrough ----

    @Test
    void fix_nullStrategies_passesNullToRuleFixer() {
        setupTraceContext();
        fixService.fix(1L, 1L, null, null);

        @SuppressWarnings("unchecked")
        ArgumentCaptor<List<String>> captor = ArgumentCaptor.forClass(List.class);
        verify(ruleFixer).fix(anyLong(), any(), any(), anyList(), anyList(), anyList(),
                anyMap(), anyLong(), anyBoolean(), anyInt(), anyBoolean(), captor.capture(), anyInt(), any());
        assertNull(captor.getValue());
    }

    @Test
    void fix_explicitStrategies_passesToRuleFixer() {
        setupTraceContext();
        fixService.fix(1L, 1L, List.of("disable"), null);

        @SuppressWarnings("unchecked")
        ArgumentCaptor<List<String>> captor = ArgumentCaptor.forClass(List.class);
        verify(ruleFixer).fix(anyLong(), any(), any(), anyList(), anyList(), anyList(),
                anyMap(), anyLong(), anyBoolean(), anyInt(), anyBoolean(), captor.capture(), anyInt(), any());
        assertEquals(List.of("disable"), captor.getValue());
    }

    // ---- P3: preferredRanges validation ----

    @Test
    void fix_invalidPreferredRangeKey_throws400() {
        Map<String, PreferredRange> ranges = Map.of("invalid_key", new PreferredRange(10, 20));
        assertThrows(BadRequestException.class,
                () -> fixService.fix(1L, 1L, null, ranges));
    }

    @Test
    void fix_validPreferredRangeKey_passes() {
        setupTraceContext();
        Map<String, PreferredRange> ranges = Map.of("r0_c1", new PreferredRange(10, 20));
        assertDoesNotThrow(() -> fixService.fix(1L, 1L, null, ranges));
    }

    @Test
    void fix_preferredRangeNullValue_throws400() {
        Map<String, PreferredRange> ranges = new java.util.HashMap<>();
        ranges.put("r0_c0", null);
        assertThrows(BadRequestException.class,
                () -> fixService.fix(1L, 1L, null, ranges));
    }

    @Test
    void fix_preferredRangeLowerGreaterThanUpper_throws400() {
        Map<String, PreferredRange> ranges = Map.of("r0_c0", new PreferredRange(40, 10));
        assertThrows(BadRequestException.class,
                () -> fixService.fix(1L, 1L, null, ranges));
    }

    @Test
    void fix_preferredRangeNullLower_throws400() {
        PreferredRange pr = new PreferredRange();
        pr.setUpper(20);
        Map<String, PreferredRange> ranges = Map.of("r0_c0", pr);
        assertThrows(BadRequestException.class,
                () -> fixService.fix(1L, 1L, null, ranges));
    }

    // ---- Template drift detection ----

    private void setupTraceContextWithCreatedAt(LocalDateTime createdAt, FixResultDto fixResult) {
        TracePo po = new TracePo();
        po.setId(1L);
        po.setUserId(1L);
        po.setRequestJson("{\"devices\":[{\"varName\":\"d1\",\"templateName\":\"t1\"}],"
                + "\"rules\":[],\"specs\":[],\"isAttack\":false,\"intensity\":0,\"enablePrivacy\":false}");
        when(traceRepository.findByIdAndUserId(1L, 1L)).thenReturn(Optional.of(po));

        TraceDto traceDto = new TraceDto();
        traceDto.setViolatedSpecId("s0");
        traceDto.setCreatedAt(createdAt);
        when(traceMapper.toDto(po)).thenReturn(traceDto);
        when(smvGenerator.buildDeviceSmvMap(anyLong(), anyList())).thenReturn(Map.of());
        when(ruleFixer.fix(anyLong(), any(), any(), anyList(), anyList(), anyList(),
                anyMap(), anyLong(), anyBoolean(), anyInt(), anyBoolean(), any(), anyInt(), any()))
                .thenReturn(fixResult);
    }

    @Test
    void fix_templateDrift_appendsWarningToSummary() {
        setupTraceContextWithCreatedAt(
                LocalDateTime.of(2025, 1, 1, 0, 0),
                FixResultDto.builder().fixable(false).summary("Original summary.").build());
        when(deviceTemplateRepository.existsModifiedAfter(anyLong(), anyList(), any()))
                .thenReturn(true);

        FixResultDto result = fixService.fix(1L, 1L, null, null);

        assertTrue(result.getSummary().contains("WARNING"));
        assertTrue(result.getSummary().startsWith("Original summary."));
    }

    @Test
    void fix_createdAtNull_skipsDriftCheck() {
        setupTraceContextWithCreatedAt(null,
                FixResultDto.builder().fixable(false).build());

        FixResultDto result = fixService.fix(1L, 1L, null, null);

        verify(deviceTemplateRepository, never()).existsModifiedAfter(anyLong(), anyList(), any());
        assertNotNull(result);
    }

    @Test
    void fix_summaryNull_driftWarningNotCorrupted() {
        setupTraceContextWithCreatedAt(
                LocalDateTime.of(2025, 1, 1, 0, 0),
                FixResultDto.builder().fixable(false).build());
        when(deviceTemplateRepository.existsModifiedAfter(anyLong(), anyList(), any()))
                .thenReturn(true);

        FixResultDto result = fixService.fix(1L, 1L, null, null);

        assertTrue(result.getSummary().startsWith("WARNING"));
        assertFalse(result.getSummary().contains("null"));
    }
}
