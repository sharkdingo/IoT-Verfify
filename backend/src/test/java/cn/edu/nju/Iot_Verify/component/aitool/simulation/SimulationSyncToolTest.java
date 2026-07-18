package cn.edu.nju.Iot_Verify.component.aitool.simulation;

import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.RunPersistenceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationResultDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.exception.ValidationException;
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
import java.util.Map;
import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.argThat;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.spy;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class SimulationSyncToolTest {

    @Mock
    private BoardDataConverter boardDataConverter;
    @Mock
    private SimulationService simulationService;

    private ObjectMapper objectMapper;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper().findAndRegisterModules();
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void simulateModel_whenResponseSerializationFails_shouldNotClaimAConclusionOrMutation() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());

        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");
        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(snapshot(device));

        SimulationResultDto result = SimulationResultDto.builder()
                .requestedSteps(10)
                .steps(10)
                .modelComplete(true)
                .states(List.of(new TraceStateDto()))
                .logs(List.of("ok"))
                .historyPersistence(RunPersistenceDto.notRequested())
                .build();
        when(simulationService.simulateWithTemplateSnapshot(anyLong(), any(), any()))
                .thenReturn(result);

        SimulateModelTool tool = new SimulateModelTool(boardDataConverter, simulationService, failingMapper);
        String response = tool.execute("{}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("RESULT_UNAVAILABLE", json.path("resultStatus").asText());
        assertEquals(false, json.path("resultAvailable").asBoolean());
        assertEquals(false, json.path("mutationMayHaveCommitted").asBoolean());
        assertTrue(json.path("message").asText().contains("No mutation was requested"));
        assertTrue(json.path("warning").asText().contains("serialization failed"));
        verify(simulationService).simulateWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void simulateModel_invalidJsonArgs_shouldReturnValidationError() throws Exception {
        SimulateModelTool tool = new SimulateModelTool(boardDataConverter, simulationService, objectMapper);

        String response = tool.execute("{");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("Invalid JSON arguments.", json.path("error").asText());
        verify(simulationService, never()).simulateWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void simulateModel_successReportsFrozenScopeAndModelTrajectoryMeaning() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");
        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(snapshot(device));
        when(simulationService.simulateWithTemplateSnapshot(anyLong(), any(), any()))
                .thenReturn(SimulationResultDto.builder()
                        .requestedSteps(1)
                        .steps(1)
                        .modelComplete(true)
                        .states(List.of(new TraceStateDto(), new TraceStateDto()))
                        .logs(List.of("ok"))
                        .historyPersistence(RunPersistenceDto.notRequested())
                        .modelSnapshot(ModelRunSnapshotDto.captured(
                                LocalDateTime.of(2026, 7, 12, 10, 0), 1, 0, 0, 0, 1))
                        .build());

        JsonNode json = objectMapper.readTree(
                new SimulateModelTool(boardDataConverter, simulationService, objectMapper)
                        .execute("{\"steps\":1}"));

        assertEquals(1, json.path("modelSnapshot").path("deviceCount").asInt());
        assertTrue(json.path("message").asText().contains("not a prediction"));
        assertTrue(json.path("message").asText().contains("not added to run history"));
        assertEquals("NOT_REQUESTED", json.path("historyPersistence").path("status").asText());
    }

    @Test
    void simulateModel_invalidSteps_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        SimulateModelTool tool = new SimulateModelTool(boardDataConverter, simulationService, objectMapper);

        String response = tool.execute("{\"steps\":101}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("steps must be between 1 and 100.", json.path("error").asText());
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(simulationService, never()).simulateWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void simulateModel_decimalSteps_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        SimulateModelTool tool = new SimulateModelTool(boardDataConverter, simulationService, objectMapper);

        String response = tool.execute("{\"steps\":3.5}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("steps must be an integer between 1 and 100.", json.path("error").asText());
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(simulationService, never()).simulateWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void simulateModel_exactModeWithoutPoints_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        SimulateModelTool tool = new SimulateModelTool(boardDataConverter, simulationService, objectMapper);

        String response = tool.execute("{\"attackMode\":\"exact\",\"attackPoints\":[]}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("attackPoints must contain between 1 and 50 points when attackMode is exact.",
                json.path("error").asText());
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(simulationService, never()).simulateWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void simulateModel_exhaustiveMode_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        SimulateModelTool tool = new SimulateModelTool(boardDataConverter, simulationService, objectMapper);

        String response = tool.execute("{\"attackMode\":\"exhaustive\"}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertTrue(json.path("error").asText().contains("attackMode must be one of"));
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(simulationService, never()).simulateWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void simulateModel_noneModeRejectsAttackPointsBeforeLoadingBoard() throws Exception {
        SimulateModelTool tool = new SimulateModelTool(boardDataConverter, simulationService, objectMapper);

        JsonNode json = objectMapper.readTree(
                tool.execute("{\"steps\":10,\"attackMode\":\"none\",\"attackPoints\":[{\"kind\":\"device\",\"deviceId\":\"d1\"}]}"));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertTrue(json.path("error").asText().contains("attackPoints must be omitted or empty"));
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(simulationService, never()).simulateWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void simulateModel_exactDevicePointNormalizesBoardOverviewId() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("living_room_light");
        device.setTemplateName("Light");
        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(snapshot(device));
        when(simulationService.simulateWithTemplateSnapshot(anyLong(), any(), any()))
                .thenReturn(SimulationResultDto.builder()
                        .requestedSteps(1)
                        .steps(1)
                        .modelComplete(true)
                        .states(List.of(new TraceStateDto(), new TraceStateDto()))
                        .logs(List.of("ok"))
                        .historyPersistence(RunPersistenceDto.notRequested())
                        .build());

        new SimulateModelTool(boardDataConverter, simulationService, objectMapper).execute("""
                {"steps":1,"attackMode":"exact","attackPoints":[
                  {"kind":"device","deviceId":"living-room-light"}
                ]}
                """);

        verify(simulationService).simulateWithTemplateSnapshot(anyLong(), argThat(request ->
                request.getAttackScenario().getPoints().get(0).getDeviceId()
                        .equals("living_room_light")), any());
    }

    @Test
    void simulateModel_serviceValidationError_shouldReturnBusinessError() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");
        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(snapshot(device));
        when(simulationService.simulateWithTemplateSnapshot(anyLong(), any(), any()))
                .thenThrow(new ValidationException("steps", "Steps must be between 1 and 100"));

        SimulateModelTool tool = new SimulateModelTool(boardDataConverter, simulationService, objectMapper);
        String response = tool.execute("{}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("BUSINESS_ERROR", json.path("errorCode").asText());
        assertEquals(422, json.path("status").asInt());
        assertTrue(json.path("error").asText().contains("Steps must be between 1 and 100"));
    }

    @Test
    void simulateModel_emptyResult_isReportedAsFailureNotCompletion() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");
        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(snapshot(device));
        when(simulationService.simulateWithTemplateSnapshot(anyLong(), any(), any()))
                .thenReturn(SimulationResultDto.builder()
                        .states(List.of())
                        .logs(List.of("No valid states parsed from simulation trace."))
                        .build());

        SimulateModelTool tool = new SimulateModelTool(boardDataConverter, simulationService, objectMapper);
        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        assertEquals("SIMULATION_FAILED", json.path("errorCode").asText());
        assertEquals("NO_TRACE_STATES", json.path("reasonCode").asText());
    }

    private ModelInputSnapshot snapshot(DeviceVerificationDto device) {
        return new ModelInputSnapshot(
                List.of(), List.of(device), List.of(), List.of(), List.of(), Map.of());
    }
}
