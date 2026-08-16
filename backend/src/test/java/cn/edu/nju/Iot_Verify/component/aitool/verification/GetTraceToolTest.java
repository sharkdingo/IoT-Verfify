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
import java.util.stream.IntStream;

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
                                .ruleIndex(0)
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
        assertEquals(0, json.path("stateOffset").asInt());
        assertEquals(10, json.path("stateLimit").asInt());
        assertEquals(1, json.path("returnedStateCount").asInt());
        assertEquals(false, json.path("hasMoreStates").asBoolean());
        assertEquals(false, json.has("trace"));
        assertEquals("Front camera", json.path("states").get(0).path("devices").get(0)
                .path("deviceLabel").asText());
        assertEquals(false, json.path("states").get(0).path("devices").get(0).has("deviceId"));
        assertEquals("Start recording on motion", json.path("states").get(0).path("triggeredRules").get(0)
                .path("ruleLabel").asText());
        assertEquals(false, json.path("states").get(0).path("triggeredRules").get(0).has("ruleId"));
        assertEquals(false, json.path("states").get(0).path("triggeredRules").get(0).has("ruleIndex"));
        assertEquals(true, json.path("message").asText().contains("incomplete"));
    }

    @Test
    void execute_pagesLongTraceInsteadOfReturningTheWholeSequence() throws Exception {
        UserContextHolder.setUserId(1L);
        TraceDto trace = TraceDto.builder()
                .id(8L)
                .modelComplete(true)
                .states(IntStream.range(0, 12)
                        .mapToObj(index -> TraceStateDto.builder()
                                .stateIndex(index)
                                .devices(List.of())
                                .triggeredRules(List.of())
                                .compromisedAutomationLinks(List.of())
                                .build())
                        .toList())
                .build();
        when(verificationService.getTrace(1L, 8L)).thenReturn(trace);

        JsonNode json = objectMapper.readTree(tool.execute(
                "{\"traceId\":8,\"stateOffset\":9,\"stateLimit\":2}"));

        assertEquals(12, json.path("stateCount").asInt());
        assertEquals(9, json.path("stateOffset").asInt());
        assertEquals(2, json.path("returnedStateCount").asInt());
        assertEquals(9, json.path("states").get(0).path("stateIndex").asInt());
        assertEquals(11, json.path("nextStateOffset").asInt());
        assertEquals(true, json.path("hasMoreStates").asBoolean());

        JsonNode beyondEnd = objectMapper.readTree(tool.execute(
                "{\"traceId\":8,\"stateOffset\":100000}"));
        assertEquals(100000, beyondEnd.path("stateOffset").asInt());
        assertEquals(0, beyondEnd.path("returnedStateCount").asInt());
        assertEquals(false, beyondEnd.path("hasMoreStates").asBoolean());
    }

    /**
     * A liveness counterexample's fault is its cycle, and the cycle is not visible in the values. NuSMV closes
     * the path by re-printing the loop entry, so the closing state equals that entry — but whether it equals
     * its own predecessor depends on the cycle length, and either way the assistant reads it wrong: a
     * one-state cycle prints no variable lines and looks like a stalled or truncated run, a longer one prints
     * the deltas back to the entry and looks like the path continuing. Paging makes recovery by comparison
     * impossible, since one window need not hold both ends.
     */
    @Test
    void execute_marksTheCycleOfALivenessCounterexample() throws Exception {
        UserContextHolder.setUserId(1L);
        SpecificationDto violatedSpec = new SpecificationDto();
        violatedSpec.setId("spec_5");
        violatedSpec.setTemplateId("5");
        TraceDto trace = TraceDto.builder()
                .id(9L)
                .violatedSpecId("spec_5")
                .violatedSpec(violatedSpec)
                .modelComplete(true)
                .states(List.of(
                        TraceStateDto.builder().stateIndex(0).build(),
                        TraceStateDto.builder().stateIndex(1).loopStart(true).build(),
                        TraceStateDto.builder().stateIndex(2).loopBack(true).build()))
                .build();
        when(verificationService.getTrace(1L, 9L)).thenReturn(trace);

        JsonNode states = objectMapper.readTree(tool.execute("{\"traceId\":9}")).path("states");

        assertEquals(3, states.size());
        assertEquals(true, states.get(1).path("loopStart").asBoolean());
        assertEquals(true, states.get(2).path("loopBack").asBoolean());
        // Absent rather than false on an ordinary state, matching how the other optional fields behave here —
        // a finite simulation or fuzz trace must not gain two always-false keys.
        assertEquals(false, states.get(0).has("loopStart"));
        assertEquals(false, states.get(0).has("loopBack"));
        assertEquals(false, states.get(1).has("loopBack"));
    }
}
