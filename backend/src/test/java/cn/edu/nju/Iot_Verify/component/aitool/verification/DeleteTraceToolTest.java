package cn.edu.nju.Iot_Verify.component.aitool.verification;

import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class DeleteTraceToolTest {

    @Mock
    private VerificationService verificationService;

    private ObjectMapper objectMapper;
    private DeleteTraceTool tool;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        tool = new DeleteTraceTool(verificationService, objectMapper);
        UserContextHolder.clear();
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void execute_withMissingTraceId_shouldReturnValidationError() throws Exception {
        UserContextHolder.setUserId(1L);
        String result = tool.execute("{}");

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
    void execute_withValidTrace_shouldDeleteSuccessfully() throws Exception {
        UserContextHolder.setUserId(1L);
        TraceDto trace = TraceDto.builder().id(8L).violatedSpecId("spec_2").build();
        when(verificationService.getTrace(1L, 8L)).thenReturn(trace);

        String result = tool.execute("{\"traceId\":8}");
        JsonNode json = objectMapper.readTree(result);

        assertEquals(true, json.path("deleted").asBoolean());
        assertEquals(8L, json.path("traceId").asLong());
        assertEquals("spec_2", json.path("violatedSpecId").asText());
        verify(verificationService).deleteTrace(1L, 8L);
    }
}
