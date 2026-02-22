package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import org.junit.jupiter.api.Test;

import java.time.LocalDateTime;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class SimulationTraceMapperTest {

    private final SimulationTraceMapper mapper = new SimulationTraceMapper();

    private SimulationTracePo samplePo() {
        return SimulationTracePo.builder()
                .id(1L)
                .userId(42L)
                .requestedSteps(10)
                .steps(3)
                .statesJson("[]")
                .logsJson("[\"log1\",\"log2\"]")
                .nusmvOutput("raw output")
                .requestJson("{}")
                .createdAt(LocalDateTime.of(2026, 1, 1, 12, 0))
                .build();
    }

    @Test
    void toDto_null_returnsNull() {
        assertNull(mapper.toDto(null));
    }

    @Test
    void toDto_mapsAllFields() {
        SimulationTraceDto dto = mapper.toDto(samplePo());

        assertEquals(1L, dto.getId());
        assertEquals(42L, dto.getUserId());
        assertEquals(10, dto.getRequestedSteps());
        assertEquals(3, dto.getSteps());
        assertNotNull(dto.getStates());
        assertTrue(dto.getStates().isEmpty());
        assertEquals(List.of("log1", "log2"), dto.getLogs());
        assertEquals("raw output", dto.getNusmvOutput());
        assertEquals("{}", dto.getRequestJson());
        assertEquals(LocalDateTime.of(2026, 1, 1, 12, 0), dto.getCreatedAt());
    }
    @Test
    void toDto_nullStatesJson_returnsEmptyList() {
        SimulationTracePo po = samplePo();
        po.setStatesJson(null);
        SimulationTraceDto dto = mapper.toDto(po);
        assertNotNull(dto.getStates());
        assertTrue(dto.getStates().isEmpty());
    }

    @Test
    void toSummaryDto_null_returnsNull() {
        assertNull(mapper.toSummaryDto(null));
    }

    @Test
    void toSummaryDto_mapsFields() {
        SimulationTraceSummaryDto dto = mapper.toSummaryDto(samplePo());

        assertEquals(1L, dto.getId());
        assertEquals(10, dto.getRequestedSteps());
        assertEquals(3, dto.getSteps());
        assertEquals(LocalDateTime.of(2026, 1, 1, 12, 0), dto.getCreatedAt());
    }

    @Test
    void toSummaryDtoList_mapsList() {
        List<SimulationTraceSummaryDto> list = mapper.toSummaryDtoList(
                List.of(samplePo(), samplePo()));
        assertEquals(2, list.size());
    }
}
