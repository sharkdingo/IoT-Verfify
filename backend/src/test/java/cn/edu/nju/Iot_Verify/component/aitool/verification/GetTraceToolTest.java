package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
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
        TraceDto trace = TraceDto.builder()
                .id(7L)
                .violatedSpecId("spec_1")
                .states(List.of(TraceStateDto.builder().stateIndex(1).devices(List.of()).build()))
                .build();
        when(verificationService.getTrace(1L, 7L)).thenReturn(trace);

        String result = tool.execute("{\"traceId\":7}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(7L, json.path("traceId").asLong());
        assertEquals("spec_1", json.path("violatedSpecId").asText());
        assertEquals(1, json.path("stateCount").asInt());
        assertEquals(7L, json.path("trace").path("id").asLong());
    }
}
