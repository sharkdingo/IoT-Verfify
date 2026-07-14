package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.dto.trace.TraceSummaryDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.verification.VerificationRunSummaryDto;
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
class ListTracesToolTest {

    @Mock
    private VerificationService verificationService;

    private ObjectMapper objectMapper;
    private ListTracesTool tool;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        tool = new ListTracesTool(verificationService, objectMapper);
        UserContextHolder.clear();
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void execute_withoutLogin_shouldReturnErrorJson() throws Exception {
        String result = tool.execute("{}");

        JsonNode json = objectMapper.readTree(result);
        assertEquals("User not logged in", json.path("error").asText());
        assertEquals("UNAUTHORIZED", json.path("errorCode").asText());
        assertEquals(401, json.path("status").asInt());
    }

    @Test
    void execute_withNoTrace_shouldReturnEmptySummary() throws Exception {
        UserContextHolder.setUserId(1L);
        when(verificationService.getRuns(1L)).thenReturn(List.of());

        String result = tool.execute("{}");

        JsonNode json = objectMapper.readTree(result);
        assertEquals(0, json.path("count").asInt());
        assertEquals("No verification traces found. Traces are created when verification detects property violations.",
                json.path("message").asText());
    }

    @Test
    void execute_withUnknownField_shouldRejectBeforeListing() throws Exception {
        UserContextHolder.setUserId(1L);
        JsonNode json = objectMapper.readTree(tool.execute("{\"limit\":10}"));

        assertEquals("VALIDATION_ERROR", json.path("errorCode").asText());
        verify(verificationService, never()).getRuns(1L);
    }

    @Test
    void execute_whenServiceThrows_shouldReturnStableErrorJson() throws Exception {
        UserContextHolder.setUserId(1L);
        when(verificationService.getRuns(1L)).thenThrow(new RuntimeException("boom\"bad"));

        String result = tool.execute("{}");

        JsonNode json = objectMapper.readTree(result);
        assertEquals("Failed to list traces.", json.path("error").asText());
        assertEquals("INTERNAL_ERROR", json.path("errorCode").asText());
        assertEquals(500, json.path("status").asInt());
    }

    @Test
    void execute_withTrace_shouldExposeSpecContextAndModelCompleteness() throws Exception {
        UserContextHolder.setUserId(1L);
        SpecificationDto violatedSpec = new SpecificationDto();
        violatedSpec.setId("spec_1");
        violatedSpec.setTemplateId("7");
        violatedSpec.setTemplateLabel("Trust safety");
        TraceSummaryDto trace = TraceSummaryDto.builder()
                .id(5L)
                .violatedSpecId("spec_1")
                .violatedSpec(violatedSpec)
                .stateCount(4)
                .dataAvailable(true)
                .build();
        VerificationRunSummaryDto run = VerificationRunSummaryDto.builder()
                .id(10L)
                .modelComplete(false)
                .disabledRuleCount(2)
                .skippedSpecCount(1)
                .dataAvailable(true)
                .counterexamples(List.of(trace))
                .build();
        when(verificationService.getRuns(1L)).thenReturn(List.of(run));

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        JsonNode item = json.path("traces").get(0);
        assertEquals(5L, item.path("traceId").asLong());
        assertEquals("Trust safety", item.path("violatedSpecification").path("specificationLabel").asText());
        assertEquals(false, item.has("violatedSpecId"));
        assertEquals(false, item.path("violatedSpecification").has("id"));
        assertEquals(false, item.path("violatedSpecification").has("templateId"));
        assertEquals(false, item.path("modelComplete").asBoolean());
        assertEquals(2, item.path("disabledRuleCount").asInt());
        assertEquals(1, item.path("skippedSpecCount").asInt());
        assertEquals(4, item.path("stateCount").asInt());
        assertEquals(1, json.path("availableCount").asInt());
        assertEquals(0, json.path("unavailableCount").asInt());
    }

    @Test
    void execute_withUnavailableTrace_shouldExplainItWithoutFabricatingDetails() throws Exception {
        UserContextHolder.setUserId(1L);
        TraceSummaryDto trace = TraceSummaryDto.builder()
                .id(6L)
                .dataAvailable(false)
                .unavailableReasonCode("PERSISTED_SEMANTIC_DATA_INVALID")
                .build();
        VerificationRunSummaryDto run = VerificationRunSummaryDto.builder()
                .id(11L)
                .dataAvailable(true)
                .counterexamples(List.of(trace))
                .build();
        when(verificationService.getRuns(1L)).thenReturn(List.of(run));

        JsonNode json = objectMapper.readTree(tool.execute("{}"));

        JsonNode item = json.path("traces").get(0);
        assertEquals(false, item.path("dataAvailable").asBoolean());
        assertEquals("PERSISTED_SEMANTIC_DATA_INVALID",
                item.path("unavailableReasonCode").asText());
        assertEquals(false, item.has("stateCount"));
        assertEquals(0, json.path("availableCount").asInt());
        assertEquals(1, json.path("unavailableCount").asInt());
    }
}
