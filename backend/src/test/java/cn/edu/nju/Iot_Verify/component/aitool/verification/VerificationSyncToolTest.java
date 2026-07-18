package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.RunPersistenceDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.verification.SpecResultDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationOutcome;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationResultDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
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
import java.util.Map;
import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.spy;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class VerificationSyncToolTest {

    @Mock
    private BoardDataConverter boardDataConverter;
    @Mock
    private VerificationService verificationService;

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
    void verifyModel_whenResponseSerializationFails_shouldNotClaimAConclusion() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());

        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(snapshot(device, spec));

        VerificationResultDto result = VerificationResultDto.builder()
                .outcome(VerificationOutcome.SATISFIED)
                .modelComplete(true)
                .specResults(List.of(SpecResultDto.builder()
                        .specId("s1")
                        .outcome(VerificationOutcome.SATISFIED)
                        .expression("CTLSPEC AG(light.on)")
                        .build()))
                .traces(List.of())
                .checkLogs(List.of("ok"))
                .historyPersistence(RunPersistenceDto.saved(10L))
                .build();
        when(verificationService.verifyWithTemplateSnapshot(anyLong(), any(), any()))
                .thenReturn(result);

        VerifyModelTool tool = new VerifyModelTool(boardDataConverter, verificationService, failingMapper);
        String response = tool.execute("{}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("RESULT_UNAVAILABLE", json.path("resultStatus").asText());
        assertEquals(false, json.path("resultAvailable").asBoolean());
        assertEquals(true, json.path("mutationMayHaveCommitted").asBoolean());
        assertTrue(json.path("message").asText().contains("Do not infer"));
        assertTrue(json.path("warning").asText().contains("serialization failed"));
        verify(verificationService).verifyWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void verifyModel_violationReportsFrozenScopeAndReadableTraceContext() throws Exception {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("dev_1");
        device.setTemplateName("Light");
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateLabel("Kitchen light must stay off");
        spec.setFormula("AG(kitchen_light.off)");
        when(boardDataConverter.getModelInputSnapshot(1L)).thenReturn(snapshot(device, spec));

        TraceDto trace = TraceDto.builder()
                .id(7L)
                .violatedSpecId("internal-spec-id")
                .violatedSpec(spec)
                .states(List.of())
                .build();

        VerificationResultDto result = VerificationResultDto.builder()
                .outcome(VerificationOutcome.VIOLATED)
                .modelComplete(true)
                .specResults(List.of(SpecResultDto.builder()
                        .specId("s1")
                        .specificationLabel("Kitchen light must stay off")
                        .formulaPreview("AG(kitchen_light.off)")
                        .formulaKind("CTL")
                        .outcome(VerificationOutcome.VIOLATED)
                        .expression("CTLSPEC AG(light.on)")
                        .build()))
                .traces(List.of(trace))
                .checkLogs(List.of("violated without trace"))
                .historyPersistence(RunPersistenceDto.outcomeUnknown(
                        "RUN_HISTORY_SAVE_OUTCOME_UNKNOWN"))
                .modelSnapshot(ModelRunSnapshotDto.captured(
                        LocalDateTime.of(2026, 7, 12, 10, 0), 1, 0, 1, 0, 1))
                .build();
        when(verificationService.verifyWithTemplateSnapshot(anyLong(), any(), any()))
                .thenReturn(result);

        VerifyModelTool tool = new VerifyModelTool(boardDataConverter, verificationService, objectMapper);
        String response = tool.execute("{}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals(1, json.path("violationCount").asInt());
        assertEquals(1, json.path("traceCount").asInt());
        assertTrue(json.path("specResults").get(0).path("specId").isMissingNode());
        assertTrue(json.path("specResults").get(0).path("templateId").isMissingNode());
        assertEquals("Kitchen light must stay off",
                json.path("specResults").get(0).path("specificationLabel").asText());
        assertEquals("CTLSPEC AG(light.on)",
                json.path("specResults").get(0).path("checkedExpression").asText());
        assertEquals("VIOLATED", json.path("specResults").get(0).path("outcome").asText());
        assertEquals(1, json.path("modelSnapshot").path("deviceCount").asInt());
        assertEquals("Kitchen light must stay off",
                json.path("traces").get(0).path("violatedSpecificationLabel").asText());
        assertEquals("AG(kitchen_light.off)",
                json.path("traces").get(0).path("formulaPreview").asText());
        assertTrue(json.path("traces").get(0).path("violatedSpecId").isMissingNode());
        assertEquals("OUTCOME_UNKNOWN", json.path("historyPersistence").path("status").asText());
        assertTrue(json.path("message").asText().contains("could not be confirmed"));
    }

    @Test
    void verifyModel_invalidJsonArgs_shouldReturnValidationError() throws Exception {
        VerifyModelTool tool = new VerifyModelTool(boardDataConverter, verificationService, objectMapper);

        String response = tool.execute("{");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("Invalid JSON arguments.", json.path("error").asText());
        verify(verificationService, never()).verifyWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void verifyModel_invalidIntensity_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        VerifyModelTool tool = new VerifyModelTool(boardDataConverter, verificationService, objectMapper);

        String response = tool.execute("{\"attackBudget\":51}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("attackBudget must be between 0 and 50.", json.path("error").asText());
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(verificationService, never()).verifyWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void verifyModel_attackEnabledWithZeroBudget_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        VerifyModelTool tool = new VerifyModelTool(boardDataConverter, verificationService, objectMapper);

        String response = tool.execute("{\"attackMode\":\"exhaustive\",\"attackBudget\":0}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("attackBudget must be between 1 and 50.", json.path("error").asText());
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(verificationService, never()).verifyWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void verifyModel_disabledAttackRejectsPositiveBudgetAndUnknownFieldsBeforeLoadingBoard() throws Exception {
        VerifyModelTool tool = new VerifyModelTool(boardDataConverter, verificationService, objectMapper);

        JsonNode positiveDisabledBudget = objectMapper.readTree(
                tool.execute("{\"attackMode\":\"none\",\"attackBudget\":3}"));
        JsonNode unknownField = objectMapper.readTree(
                tool.execute("{\"attackMode\":\"none\",\"isAttack\":false}"));

        assertEquals("VALIDATION_ERROR", positiveDisabledBudget.path("errorCode").asText());
        assertTrue(positiveDisabledBudget.path("error").asText().contains("attackMode is none"));
        assertEquals("VALIDATION_ERROR", unknownField.path("errorCode").asText());
        assertTrue(unknownField.path("error").asText().contains("isAttack"));
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(verificationService, never()).verifyWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void verifyModel_hugePositiveIntensity_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        VerifyModelTool tool = new VerifyModelTool(boardDataConverter, verificationService, objectMapper);

        String response = tool.execute("{\"attackBudget\":4294967299}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("attackBudget must be between 0 and 50.", json.path("error").asText());
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(verificationService, never()).verifyWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void verifyModel_hugeNegativeIntensity_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        VerifyModelTool tool = new VerifyModelTool(boardDataConverter, verificationService, objectMapper);

        String response = tool.execute("{\"attackBudget\":-4294967299}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("attackBudget must be between 0 and 50.", json.path("error").asText());
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(verificationService, never()).verifyWithTemplateSnapshot(anyLong(), any(), any());
    }

    @Test
    void verifyModel_stringIntensity_shouldReturnValidationErrorBeforeLoadingBoard() throws Exception {
        VerifyModelTool tool = new VerifyModelTool(boardDataConverter, verificationService, objectMapper);

        String response = tool.execute("{\"attackBudget\":\"3\"}");
        JsonNode json = objectMapper.readTree(response);

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
        assertEquals("attackBudget must be an integer between 0 and 50.", json.path("error").asText());
        verify(boardDataConverter, never()).getModelInputSnapshot(anyLong());
        verify(verificationService, never()).verifyWithTemplateSnapshot(anyLong(), any(), any());
    }

    private ModelInputSnapshot snapshot(DeviceVerificationDto device, SpecificationDto spec) {
        return new ModelInputSnapshot(
                List.of(), List.of(device), List.of(), List.of(), List.of(spec), Map.of());
    }
}
