package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class SimulationTraceToolsTest {

    @Mock
    private SimulationService simulationService;

    private ObjectMapper objectMapper;
    private ListSimulationTracesTool listTool;
    private GetSimulationTraceTool getTool;
    private DeleteSimulationTraceTool deleteTool;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        listTool = new ListSimulationTracesTool(simulationService, objectMapper);
        getTool = new GetSimulationTraceTool(simulationService, objectMapper);
        deleteTool = new DeleteSimulationTraceTool(simulationService, objectMapper);
        UserContextHolder.clear();
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void listSimulations_withoutLogin_shouldReturnErrorJson() throws Exception {
        String result = listTool.execute("{}");

        JsonNode json = objectMapper.readTree(result);
        assertEquals("UNAUTHORIZED", json.path("errorCode").asText());
        assertEquals(401, json.path("status").asInt());
    }

    @Test
    void listSimulations_withNoData_shouldReturnEmptySummary() throws Exception {
        UserContextHolder.setUserId(1L);
        when(simulationService.getUserSimulations(1L)).thenReturn(List.of());

        String result = listTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(0, json.path("count").asInt());
        assertTrue(json.path("message").asText().contains("No simulation traces found"));
    }

    @Test
    void listSimulations_whenServiceReturnsNull_shouldFallbackToEmptySummary() throws Exception {
        UserContextHolder.setUserId(1L);
        when(simulationService.getUserSimulations(1L)).thenReturn(null);

        String result = listTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(0, json.path("count").asInt());
        assertTrue(json.path("message").asText().contains("No simulation traces found"));
    }

    @Test
    void listSimulations_withData_shouldReturnSummaries() throws Exception {
        UserContextHolder.setUserId(1L);
        when(simulationService.getUserSimulations(1L)).thenReturn(List.of(
                SimulationTraceSummaryDto.builder().id(3L).requestedSteps(10).steps(9).build()
        ));

        String result = listTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(1, json.path("count").asInt());
        assertEquals(3L, json.path("traces").get(0).path("id").asLong());
    }

    @Test
    void getSimulationTrace_withInvalidJson_shouldReturnValidationError() throws Exception {
        UserContextHolder.setUserId(1L);
        String result = getTool.execute("{invalid");

        JsonNode json = objectMapper.readTree(result);
        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
    }

    @Test
    void getSimulationTrace_withoutIncludeRaw_shouldHideRawFields() throws Exception {
        UserContextHolder.setUserId(1L);
        SimulationTraceDto trace = SimulationTraceDto.builder()
                .id(11L)
                .requestedSteps(12)
                .steps(12)
                .states(List.of())
                .logs(List.of("ok"))
                .nusmvOutput("raw-output")
                .requestJson("{\"steps\":12}")
                .build();
        when(simulationService.getSimulation(1L, 11L)).thenReturn(trace);

        String result = getTool.execute("{\"simulationId\":11}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(11L, json.path("simulationId").asLong());
        assertFalse(json.path("trace").has("nusmvOutput"));
        assertFalse(json.path("trace").has("requestJson"));
    }

    @Test
    void getSimulationTrace_withIncludeRaw_shouldKeepRawFields() throws Exception {
        UserContextHolder.setUserId(1L);
        SimulationTraceDto trace = SimulationTraceDto.builder()
                .id(12L)
                .requestedSteps(8)
                .steps(8)
                .states(List.of())
                .logs(List.of("ok"))
                .nusmvOutput("raw-output")
                .requestJson("{\"steps\":8}")
                .build();
        when(simulationService.getSimulation(1L, 12L)).thenReturn(trace);

        String result = getTool.execute("{\"simulationId\":12,\"includeRaw\":true}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("raw-output", json.path("trace").path("nusmvOutput").asText());
        assertTrue(json.path("trace").path("requestJson").asText().contains("\"steps\":8"));
    }

    @Test
    void getSimulationTrace_withNotFoundId_shouldReturnBusinessError() throws Exception {
        UserContextHolder.setUserId(1L);
        when(simulationService.getSimulation(1L, 404L))
                .thenThrow(new ResourceNotFoundException("SimulationTrace", 404L));

        String result = getTool.execute("{\"simulationId\":404}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("BUSINESS_ERROR", json.path("errorCode").asText());
        assertEquals(404, json.path("status").asInt());
    }

    @Test
    void deleteSimulationTrace_shouldPrecheckAndDelete() throws Exception {
        UserContextHolder.setUserId(1L);
        SimulationTraceDto trace = SimulationTraceDto.builder().id(13L).steps(6).build();
        when(simulationService.getSimulation(1L, 13L)).thenReturn(trace);

        String result = deleteTool.execute("{\"simulationId\":13}");
        JsonNode json = objectMapper.readTree(result);

        assertTrue(json.path("deleted").asBoolean());
        assertEquals(13L, json.path("simulationId").asLong());
        verify(simulationService).deleteSimulation(1L, 13L);
    }

    @Test
    void deleteSimulationTrace_withNotFoundId_shouldReturnBusinessError() throws Exception {
        UserContextHolder.setUserId(1L);
        when(simulationService.getSimulation(1L, 404L))
                .thenThrow(new ResourceNotFoundException("SimulationTrace", 404L));

        String result = deleteTool.execute("{\"simulationId\":404}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("BUSINESS_ERROR", json.path("errorCode").asText());
        assertEquals(404, json.path("status").asInt());
    }
}
