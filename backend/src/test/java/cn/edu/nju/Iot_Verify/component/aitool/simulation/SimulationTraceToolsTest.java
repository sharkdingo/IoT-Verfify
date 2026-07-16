package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.component.aitool.AiDestructiveActionGuard;
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
import static org.mockito.Mockito.never;
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
        AiDestructiveActionGuard destructiveActionGuard = new AiDestructiveActionGuard(objectMapper);
        listTool = new ListSimulationTracesTool(simulationService, objectMapper);
        getTool = new GetSimulationTraceTool(simulationService, objectMapper);
        deleteTool = new DeleteSimulationTraceTool(
                simulationService, objectMapper, destructiveActionGuard);
        UserContextHolder.clear();
        UserContextHolder.setChatSessionId("simulation-trace-test-session");
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
    void listSimulations_withUnknownField_shouldRejectBeforeListing() throws Exception {
        UserContextHolder.setUserId(1L);
        JsonNode json = objectMapper.readTree(listTool.execute("{\"limit\":10}"));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        verify(simulationService, never()).getUserSimulations(1L);
    }

    @Test
    void listSimulations_withData_shouldReturnSummaries() throws Exception {
        UserContextHolder.setUserId(1L);
        when(simulationService.getUserSimulations(1L)).thenReturn(List.of(
                SimulationTraceSummaryDto.builder()
                        .id(3L)
                        .requestedSteps(10)
                        .steps(9)
                        .modelComplete(false)
                        .disabledRuleCount(1)
                        .attack(true)
                        .attackBudget(2)
                        .enablePrivacy(true)
                        .build()
        ));

        String result = listTool.execute("{}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(1, json.path("count").asInt());
        assertEquals(3L, json.path("traces").get(0).path("simulationId").asLong());
        assertFalse(json.path("traces").get(0).path("modelComplete").asBoolean());
        assertEquals(1, json.path("traces").get(0).path("disabledRuleCount").asInt());
        assertTrue(json.path("traces").get(0).path("isAttack").asBoolean());
        assertEquals(1, json.path("availableCount").asInt());
        assertEquals(0, json.path("unavailableCount").asInt());
    }

    @Test
    void listSimulations_withUnavailableRow_shouldReturnReasonWithoutDefaultRunDetails() throws Exception {
        UserContextHolder.setUserId(1L);
        when(simulationService.getUserSimulations(1L)).thenReturn(List.of(
                SimulationTraceSummaryDto.builder()
                        .id(4L)
                        .dataAvailable(false)
                        .unavailableReasonCode("PERSISTED_SEMANTIC_DATA_INVALID")
                        .build()));

        JsonNode json = objectMapper.readTree(listTool.execute("{}"));

        JsonNode item = json.path("traces").get(0);
        assertEquals(false, item.path("dataAvailable").asBoolean());
        assertEquals("PERSISTED_SEMANTIC_DATA_INVALID",
                item.path("unavailableReasonCode").asText());
        assertEquals(false, item.has("steps"));
        assertEquals(0, json.path("availableCount").asInt());
        assertEquals(1, json.path("unavailableCount").asInt());
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
    void getAndDeleteSimulationTrace_withUnknownField_shouldRejectBeforeLoading() throws Exception {
        UserContextHolder.setUserId(1L);
        JsonNode get = objectMapper.readTree(getTool.execute(
                "{\"simulationId\":11,\"raw\":true}"));
        JsonNode delete = objectMapper.readTree(deleteTool.execute(
                "{\"simulationId\":11,\"confirmed\":false,\"force\":true}"));

        assertEquals("VALIDATION_ERROR", get.path("errorCode").asText());
        assertEquals("VALIDATION_ERROR", delete.path("errorCode").asText());
        verify(simulationService, never()).getSimulation(1L, 11L);
    }

    @Test
    void getSimulationTrace_shouldReturnUserSemanticStateProjection() throws Exception {
        UserContextHolder.setUserId(1L);
        cn.edu.nju.Iot_Verify.dto.trace.TraceDeviceDto device = new cn.edu.nju.Iot_Verify.dto.trace.TraceDeviceDto();
        device.setDeviceId("light_internal");
        device.setDeviceLabel("Hall light");
        device.setTemplateName("Light");
        SimulationTraceDto trace = SimulationTraceDto.builder()
                .id(11L)
                .requestedSteps(12)
                .steps(12)
                .modelComplete(false)
                .disabledRuleCount(1)
                .attack(true)
                .attackBudget(2)
                .enablePrivacy(true)
                .states(List.of(cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto.builder()
                        .stateIndex(0)
                        .devices(List.of(device))
                        .triggeredRules(List.of(cn.edu.nju.Iot_Verify.dto.trace.TraceTriggeredRuleDto.builder()
                                .ruleId("7")
                                .ruleLabel("Turn on hall light")
                                .build()))
                        .compromisedAutomationLinks(List.of())
                        .build()))
                .logs(List.of("ok"))
                .nusmvOutput("raw-output")
                .requestJson("{\"steps\":12}")
                .build();
        when(simulationService.getSimulation(1L, 11L)).thenReturn(trace);

        String result = getTool.execute("{\"simulationId\":11}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(11L, json.path("simulationId").asLong());
        assertFalse(json.has("nusmvOutput"));
        assertFalse(json.has("requestJson"));
        assertFalse(json.path("modelComplete").asBoolean());
        assertEquals(1, json.path("disabledRuleCount").asInt());
        assertTrue(json.path("isAttack").asBoolean());
        assertEquals("Hall light", json.path("states").get(0).path("devices").get(0)
                .path("deviceLabel").asText());
        assertFalse(json.path("states").get(0).path("devices").get(0).has("deviceId"));
        assertEquals("Turn on hall light", json.path("states").get(0).path("triggeredRules").get(0)
                .path("ruleLabel").asText());
        assertFalse(json.path("states").get(0).path("triggeredRules").get(0).has("ruleId"));
        assertTrue(json.path("message").asText().contains("incomplete"));
    }

    @Test
    void getSimulationTrace_withIncludeRaw_shouldRejectTechnicalEscapeHatch() throws Exception {
        UserContextHolder.setUserId(1L);
        JsonNode json = objectMapper.readTree(getTool.execute(
                "{\"simulationId\":12,\"includeRaw\":true}"));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        verify(simulationService, never()).getSimulation(1L, 12L);
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

        String preview = deleteTool.execute("{\"simulationId\":13,\"confirmed\":false}");
        JsonNode previewJson = objectMapper.readTree(preview);
        assertTrue(previewJson.path("requiresUserConfirmation").asBoolean());
        verify(simulationService, never()).deleteSimulation(1L, 13L);

        UserContextHolder.setDestructiveActionConfirmed(true);
        String result = deleteTool.execute("{\"simulationId\":13,\"confirmed\":true,\"impactToken\":\""
                + previewJson.path("impactToken").asText() + "\"}");
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

        String result = deleteTool.execute("{\"simulationId\":404,\"confirmed\":false}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("BUSINESS_ERROR", json.path("errorCode").asText());
        assertEquals(404, json.path("status").asInt());
    }
}
