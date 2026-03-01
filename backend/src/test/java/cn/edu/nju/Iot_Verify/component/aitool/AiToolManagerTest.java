package cn.edu.nju.Iot_Verify.component.aitool;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class AiToolManagerTest {

    @Mock
    private AiTool knownTool;

    private ObjectMapper objectMapper;
    private AiToolManager manager;

    @BeforeEach
    void setUp() {
        objectMapper = new ObjectMapper();
        when(knownTool.getName()).thenReturn("known_tool");
        manager = new AiToolManager(List.of(knownTool), objectMapper);
        manager.init();
    }

    @Test
    void execute_unknownTool_shouldReturnValidJsonError() throws Exception {
        String result = manager.execute("unknown\"tool", "{}");

        JsonNode json = objectMapper.readTree(result);
        assertEquals("Unknown function: unknown\"tool", json.path("error").asText());
        assertEquals("TOOL_NOT_FOUND", json.path("errorCode").asText());
        assertEquals(404, json.path("status").asInt());
    }

    @Test
    void execute_knownTool_shouldDelegateToTool() {
        when(knownTool.execute("{\"x\":1}")).thenReturn("{\"ok\":true}");

        String result = manager.execute("known_tool", "{\"x\":1}");

        assertTrue(result.contains("\"ok\":true"));
        verify(knownTool).execute("{\"x\":1}");
    }
}
