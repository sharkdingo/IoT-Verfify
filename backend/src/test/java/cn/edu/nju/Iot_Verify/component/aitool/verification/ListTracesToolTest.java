package cn.edu.nju.Iot_Verify.component.aitool.verification;

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
        when(verificationService.getUserTraces(1L)).thenReturn(List.of());

        String result = tool.execute("{}");

        JsonNode json = objectMapper.readTree(result);
        assertEquals(0, json.path("count").asInt());
        assertEquals("No verification traces found. Traces are created when verification detects property violations.",
                json.path("message").asText());
    }

    @Test
    void execute_whenServiceThrows_shouldReturnStableErrorJson() throws Exception {
        UserContextHolder.setUserId(1L);
        when(verificationService.getUserTraces(1L)).thenThrow(new RuntimeException("boom\"bad"));

        String result = tool.execute("{}");

        JsonNode json = objectMapper.readTree(result);
        assertEquals("Failed to list traces.", json.path("error").asText());
        assertEquals("INTERNAL_ERROR", json.path("errorCode").asText());
        assertEquals(500, json.path("status").asInt());
    }
}
