package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.exception.PersistedDataIntegrityException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.datatype.jsr310.JavaTimeModule;
import org.junit.jupiter.api.Test;

import java.time.LocalDateTime;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class SimulationTraceMapperTest {

    private final SimulationTraceMapper mapper = new SimulationTraceMapper();
    private static final String MODEL_SNAPSHOT_JSON = "{\"capturedAt\":\"2026-07-12T09:30:00\","
            + "\"deviceCount\":1,\"ruleCount\":1,\"specificationCount\":0,"
            + "\"environmentVariableCount\":0,\"deviceTemplateCount\":1,\"templatesFrozen\":true}";

    private SimulationTracePo samplePo() {
        return SimulationTracePo.builder()
                .id(1L)
                .userId(42L)
                .requestedSteps(10)
                .steps(3)
                .statesJson("[{}]")
                .logsJson("[\"log1\",\"log2\"]")
                .nusmvOutput("raw output")
                .requestJson("{\"devices\":[],\"rules\":[],\"steps\":10,\"isAttack\":true,\"attackBudget\":2,\"enablePrivacy\":true}")
                .templateSnapshotsJson("{\"light\":{\"Name\":\"Light\"}}")
                .modelSnapshotJson(MODEL_SNAPSHOT_JSON)
                .isAttack(true)
                .attackBudget(2)
                .enablePrivacy(true)
                .modeledDeviceAttackPointCount(1)
                .modeledFalsifiableReadingDeviceCount(1)
                .modeledAutomationLinkAttackPointCount(2)
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
        assertEquals(1, dto.getStates().size());
        assertEquals(List.of("log1", "log2"), dto.getLogs());
        assertEquals("raw output", dto.getNusmvOutput());
        assertTrue(dto.getRequestJson().contains("\"isAttack\":true"));
        assertEquals(Boolean.TRUE, dto.getAttack());
        assertEquals(2, dto.getAttackBudget());
        assertEquals(Boolean.TRUE, dto.getEnablePrivacy());
        assertEquals(1, dto.getModelSemantics().getModeledDeviceAttackPointCount());
        assertEquals(1, dto.getModelSemantics().getModeledFalsifiableReadingDeviceCount());
        assertEquals(2, dto.getModelSemantics().getModeledAutomationLinkAttackPointCount());
        assertEquals(1, dto.getModelSnapshot().getDeviceCount());
        assertTrue(dto.getModelSnapshot().isTemplatesFrozen());
        assertEquals("{\"light\":{\"Name\":\"Light\"}}", dto.getTemplateSnapshotsJson());
        assertEquals(LocalDateTime.of(2026, 1, 1, 12, 0), dto.getCreatedAt());
    }

    @Test
    void toDto_hidesInternalOwnershipAndRequestSnapshotFromJson() {
        ObjectMapper objectMapper = new ObjectMapper().registerModule(new JavaTimeModule());
        JsonNode json = objectMapper.valueToTree(mapper.toDto(samplePo()));

        assertFalse(json.has("userId"));
        assertFalse(json.has("requestJson"));
        assertFalse(json.has("templateSnapshotsJson"));
        assertTrue(json.path("modelSnapshot").path("templatesFrozen").asBoolean());
        assertTrue(json.path("isAttack").asBoolean());
        assertEquals(2, json.path("attackBudget").asInt());
    }
    @Test
    void toDto_nullStatesJson_failsClosed() {
        SimulationTracePo po = samplePo();
        po.setStatesJson(null);
        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));
        assertEquals("statesJson", error.getField());
    }

    @Test
    void toDto_emptyStatesJson_failsClosed() {
        SimulationTracePo po = samplePo();
        po.setStatesJson("[]");
        PersistedDataIntegrityException error = assertThrows(
                PersistedDataIntegrityException.class, () -> mapper.toDto(po));
        assertEquals("statesJson", error.getField());
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
        assertEquals(Boolean.TRUE, dto.getAttack());
        assertEquals(2, dto.getAttackBudget());
        assertEquals(Boolean.TRUE, dto.getEnablePrivacy());
        assertEquals(1, dto.getModelSnapshot().getDeviceCount());
        assertEquals(LocalDateTime.of(2026, 1, 1, 12, 0), dto.getCreatedAt());
    }

    @Test
    void toSummaryDtoList_mapsList() {
        List<SimulationTraceSummaryDto> list = mapper.toSummaryDtoList(
                List.of(samplePo(), samplePo()));
        assertEquals(2, list.size());
    }

    @Test
    void toSummaryDtoList_keepsCorruptItemAsUnavailablePlaceholder() {
        SimulationTracePo corrupt = samplePo();
        corrupt.setId(2L);
        corrupt.setModelSnapshotJson("{not-json}");

        List<SimulationTraceSummaryDto> list = mapper.toSummaryDtoList(
                List.of(samplePo(), corrupt));

        assertEquals(2, list.size());
        assertTrue(list.get(0).getDataAvailable());
        assertFalse(list.get(1).getDataAvailable());
        assertEquals(2L, list.get(1).getId());
        assertEquals("PERSISTED_SEMANTIC_DATA_INVALID", list.get(1).getUnavailableReasonCode());
    }

    @Test
    void toSummaryDtoList_marksMissingPlaybackStatesUnavailable() {
        SimulationTracePo corrupt = samplePo();
        corrupt.setId(3L);
        corrupt.setStatesJson("[]");

        List<SimulationTraceSummaryDto> list = mapper.toSummaryDtoList(List.of(corrupt));

        assertEquals(1, list.size());
        assertFalse(list.get(0).getDataAvailable());
        assertEquals("PERSISTED_SEMANTIC_DATA_INVALID", list.get(0).getUnavailableReasonCode());
    }
}
