package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.dto.fix.PreferredRangeSelection;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.FixService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class FixViolationToolTest {

    @Mock private FixService fixService;
    private ObjectMapper objectMapper;
    private FixViolationTool tool;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        tool = new FixViolationTool(fixService, objectMapper);
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    private void assertValidationError(String argsJson) throws Exception {
        String result = tool.execute(argsJson);
        JsonNode node = objectMapper.readTree(result);
        assertEquals("VALIDATION_ERROR", node.get("errorCode").asText());
        assertEquals(400, node.get("status").asInt());
        verifyNoInteractions(fixService);
    }

    @Test
    void execute_traceId_outOfLongRange_returns400() throws Exception {
        assertValidationError("{\"traceId\":99999999999999999999}");
    }

    @Test
    void execute_legacyPreferredRanges_returns400() throws Exception {
        assertValidationError("{\"traceId\":1,\"preferredRanges\":{\"r0_c0\":{\"lower\":1,\"upper\":10}}}");
    }

    @Test
    void execute_preferredRangeSelections_nonIntegerValue_returns400() throws Exception {
        String targetId = PreferredRangeSelection.targetIdFor(0, 0);
        assertValidationError("{\"traceId\":1,\"preferredRangeSelections\":[{\"targetId\":\""
                + targetId + "\",\"lower\":\"abc\",\"upper\":10}]}");
    }

    @Test
    void execute_preferredRangeSelections_decimalValue_returns400() throws Exception {
        String targetId = PreferredRangeSelection.targetIdFor(0, 0);
        assertValidationError("{\"traceId\":1,\"preferredRangeSelections\":[{\"targetId\":\""
                + targetId + "\",\"lower\":1.5,\"upper\":10}]}");
    }

    @Test
    void execute_preferredRangeSelections_outOfIntRange_returns400() throws Exception {
        String targetId = PreferredRangeSelection.targetIdFor(0, 0);
        assertValidationError("{\"traceId\":1,\"preferredRangeSelections\":[{\"targetId\":\""
                + targetId + "\",\"lower\":4294967299,\"upper\":10}]}");
    }

    @Test
    void execute_preferredRangeSelections_invalidTargetId_returns400() throws Exception {
        assertValidationError("{\"traceId\":1,\"preferredRangeSelections\":[{\"targetId\":\"not-a-target\",\"lower\":1,\"upper\":10}]}");
    }

    @Test
    void execute_preferredRangeSelections_missingField_returns400() throws Exception {
        assertValidationError("{\"traceId\":1,\"preferredRangeSelections\":[{\"lower\":10,\"upper\":20}]}");
    }

    @Test
    void execute_preferredRangeSelections_wrongType_returns400() throws Exception {
        assertValidationError("{\"traceId\":1,\"preferredRangeSelections\":\"abc\"}");
    }

    @Test
    void execute_strategiesWrongType_doesNotFallBackToDefaultOrder() throws Exception {
        assertValidationError("{\"traceId\":1,\"strategies\":\"remove\"}");
    }

    @Test
    void execute_emptyStrategies_doesNotFallBackToDefaultOrder() throws Exception {
        assertValidationError("{\"traceId\":1,\"strategies\":[]}");
    }

    @Test
    void execute_unsupportedStrategy_returns400() throws Exception {
        assertValidationError("{\"traceId\":1,\"strategies\":[\"unknown\"]}");
    }

    @Test
    void execute_successOmitsInternalSpecIdAndExplainsThatNothingWasApplied() throws Exception {
        when(fixService.fix(anyLong(), anyLong(), any(), any())).thenReturn(FixResultDto.builder()
                .traceId(1L)
                .violatedSpecId("internal-spec-id")
                .fixable(false)
                .faultRules(java.util.List.of())
                .suggestions(java.util.List.of())
                .strategyAttempts(java.util.List.of())
                .warnings(java.util.List.of())
                .summary("No forward-verified suggestion was found; no Board change was applied.")
                .build());

        JsonNode node = objectMapper.readTree(tool.execute("{\"traceId\":1}"));

        assertFalse(node.has("violatedSpecId"));
        assertTrue(node.path("message").asText().contains("no Board change was applied"));
    }

    @Test
    void execute_serviceThrowsResourceNotFound_returns404() throws Exception {
        when(fixService.fix(anyLong(), anyLong(), any(), any()))
                .thenThrow(new ResourceNotFoundException("Trace 99 not found"));

        String result = tool.execute("{\"traceId\":99}");
        JsonNode node = objectMapper.readTree(result);

        assertEquals("NOT_FOUND", node.get("errorCode").asText());
        assertEquals(404, node.get("status").asInt());
    }

    @Test
    void execute_serviceThrowsServiceUnavailable_returns503() throws Exception {
        when(fixService.fix(anyLong(), anyLong(), any(), any()))
                .thenThrow(new ServiceUnavailableException("NuSMV busy"));

        String result = tool.execute("{\"traceId\":1}");
        JsonNode node = objectMapper.readTree(result);

        assertEquals("SERVICE_UNAVAILABLE", node.get("errorCode").asText());
        assertEquals(503, node.get("status").asInt());
    }

    @Test
    void execute_serviceThrowsSmvGenerationException_returns500WithCategory() throws Exception {
        when(fixService.fix(anyLong(), anyLong(), any(), any()))
                .thenThrow(SmvGenerationException.deviceNotFound("sensor1"));

        String result = tool.execute("{\"traceId\":1}");
        JsonNode node = objectMapper.readTree(result);

        assertEquals("SMV_GENERATION_ERROR", node.get("errorCode").asText());
        assertEquals(500, node.get("status").asInt());
        assertEquals("DEVICE_NOT_FOUND", node.get("errorCategory").asText());
    }

    @Test
    void execute_serviceThrowsGenericException_returns500FixedMessage() throws Exception {
        when(fixService.fix(anyLong(), anyLong(), any(), any()))
                .thenThrow(new RuntimeException("internal details leaked"));

        String result = tool.execute("{\"traceId\":1}");
        JsonNode node = objectMapper.readTree(result);

        assertEquals("INTERNAL_ERROR", node.get("errorCode").asText());
        assertEquals(500, node.get("status").asInt());
        assertEquals("Fix analysis failed.", node.get("error").asText(),
                "Internal details must not leak to AI response");
    }
}
