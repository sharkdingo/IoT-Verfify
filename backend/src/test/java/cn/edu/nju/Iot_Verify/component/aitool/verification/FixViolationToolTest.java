package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.exception.ResourceNotFoundException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
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
    void execute_preferredRanges_nonIntegerValue_returns400() throws Exception {
        assertValidationError("{\"traceId\":1,\"preferredRanges\":{\"r0_c0\":{\"lower\":\"abc\",\"upper\":10}}}");
    }

    @Test
    void execute_preferredRanges_decimalValue_returns400() throws Exception {
        assertValidationError("{\"traceId\":1,\"preferredRanges\":{\"r0_c0\":{\"lower\":1.5,\"upper\":10}}}");
    }

    @Test
    void execute_preferredRanges_missingField_returns400() throws Exception {
        assertValidationError("{\"traceId\":1,\"preferredRanges\":{\"r0_c0\":{\"lower\":10}}}");
    }

    @Test
    void execute_preferredRanges_wrongType_returns400() throws Exception {
        assertValidationError("{\"traceId\":1,\"preferredRanges\":\"abc\"}");
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
