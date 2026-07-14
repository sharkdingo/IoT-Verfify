package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDeviceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceTriggeredRuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class GetTraceToolTest {

    @Mock
    private VerificationService verificationService;

    private ObjectMapper objectMapper;
    private GetTraceTool tool;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        tool = new GetTraceTool(verificationService, objectMapper);
        UserContextHolder.clear();
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void execute_withoutLogin_shouldReturnErrorJson() throws Exception {
        String result = tool.execute("{\"traceId\":1}");

        JsonNode json = objectMapper.readTree(result);
        assertEquals("UNAUTHORIZED", json.path("errorCode").asText());
        assertEquals(401, json.path("status").asInt());
    }

    @Test
    void execute_withInvalidTraceId_shouldReturnValidationError() throws Exception {
        UserContextHolder.setUserId(1L);
        String result = tool.execute("{\"traceId\":0}");

        JsonNode json = objectMapper.readTree(result);
        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        assertEquals(400, json.path("status").asInt());
    }

    @Test
    void execute_withUnknownField_shouldRejectBeforeLoadingTrace() throws Exception {
        UserContextHolder.setUserId(1L);
        JsonNode json = objectMapper.readTree(tool.execute("{\"traceId\":1,\"raw\":true}"));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        verify(verificationService, never()).getTrace(1L, 1L);
    }

    @Test
    void execute_withNotFoundTrace_shouldReturnBusinessError() throws Exception {
        UserContextHolder.setUserId(1L);
        when(verificationService.getTrace(1L, 99L))
                .thenThrow(new ResourceNotFoundException("Trace", 99L));

        String result = tool.execute("{\"traceId\":99}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals("BUSINESS_ERROR", json.path("errorCode").asText());
        assertEquals(404, json.path("status").asInt());
    }

    @Test
    void execute_withValidTrace_shouldReturnTraceDetails() throws Exception {
        UserContextHolder.setUserId(1L);
        SpecificationDto violatedSpec = new SpecificationDto();
        violatedSpec.setId("spec_1");
        violatedSpec.setTemplateId("3");
        violatedSpec.setTemplateLabel("Never");
        violatedSpec.setFormula("AG(!camera.recording)");
        TraceDeviceDto device = new TraceDeviceDto();
        device.setDeviceId("camera_internal");
        device.setDeviceLabel("Front camera");
        device.setTemplateName("Camera");
        TraceDto trace = TraceDto.builder()
                .id(7L)
                .violatedSpecId("spec_1")
                .violatedSpec(violatedSpec)
                .checkedExpression("CTLSPEC AG(!camera_internal.recording)")
                .modelComplete(false)
                .disabledRuleCount(1)
                .skippedSpecCount(0)
                .states(List.of(TraceStateDto.builder()
                        .stateIndex(1)
                        .devices(List.of(device))
                        .triggeredRules(List.of(TraceTriggeredRuleDto.builder()
                                .ruleId("42")
                                .ruleLabel("Start recording on motion")
                                .build()))
                        .compromisedAutomationLinks(List.of())
                        .build()))
                .build();
        when(verificationService.getTrace(1L, 7L)).thenReturn(trace);

        String result = tool.execute("{\"traceId\":7}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(7L, json.path("traceId").asLong());
        assertEquals(false, json.has("violatedSpecId"));
        assertEquals("Never", json.path("violatedSpecification").path("specificationLabel").asText());
        assertEquals("CTL", json.path("violatedSpecification").path("formulaKind").asText());
        assertEquals(false, json.path("modelComplete").asBoolean());
        assertEquals(1, json.path("disabledRuleCount").asInt());
        assertEquals(1, json.path("stateCount").asInt());
        assertEquals(false, json.has("trace"));
        assertEquals("Front camera", json.path("states").get(0).path("devices").get(0)
                .path("deviceLabel").asText());
        assertEquals(false, json.path("states").get(0).path("devices").get(0).has("deviceId"));
        assertEquals("Start recording on motion", json.path("states").get(0).path("triggeredRules").get(0)
                .path("ruleLabel").asText());
        assertEquals(false, json.path("states").get(0).path("triggeredRules").get(0).has("ruleId"));
        assertEquals(true, json.path("message").asText().contains("incomplete"));
    }
}
