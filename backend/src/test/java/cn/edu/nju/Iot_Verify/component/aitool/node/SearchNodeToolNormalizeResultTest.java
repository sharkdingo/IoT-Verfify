package cn.edu.nju.Iot_Verify.component.aitool.node;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for SearchNodeTool.normalizeResult() — FIX-3 regression.
 * Uses reflection to test the private method directly, avoiding the need to mock NodeService.
 */
class SearchNodeToolNormalizeResultTest {

    private final ObjectMapper objectMapper = new ObjectMapper();
    private SearchNodeTool tool;
    private Method normalizeResult;

    @BeforeEach
    void setUp() throws Exception {
        tool = new SearchNodeTool(null, objectMapper);
        normalizeResult = SearchNodeTool.class.getDeclaredMethod("normalizeResult", String.class);
        normalizeResult.setAccessible(true);
    }

    private String invoke(String raw) throws Exception {
        return (String) normalizeResult.invoke(tool, raw);
    }

    @Test
    @DisplayName("null input returns empty count/devices")
    void nullInput_returnsEmpty() throws Exception {
        String result = invoke(null);
        JsonNode node = objectMapper.readTree(result);
        assertEquals(0, node.get("count").asInt());
        assertTrue(node.get("devices").isArray());
        assertEquals(0, node.get("devices").size());
    }

    @Test
    @DisplayName("blank input returns empty count/devices")
    void blankInput_returnsEmpty() throws Exception {
        String result = invoke("   ");
        JsonNode node = objectMapper.readTree(result);
        assertEquals(0, node.get("count").asInt());
    }

    @Test
    @DisplayName("JSON array input is wrapped with count")
    void jsonArray_wrappedWithCount() throws Exception {
        String result = invoke("[{\"name\":\"dev1\"},{\"name\":\"dev2\"}]");
        JsonNode node = objectMapper.readTree(result);
        assertEquals(2, node.get("count").asInt());
        assertTrue(node.get("devices").isArray());
        assertEquals(2, node.get("devices").size());
        assertEquals("dev1", node.get("devices").get(0).get("name").asText());
    }

    @Test
    @DisplayName("JSON object input is returned as-is")
    void jsonObject_returnedAsIs() throws Exception {
        String input = "{\"count\":1,\"devices\":[{\"name\":\"dev1\"}]}";
        String result = invoke(input);
        // Should return the raw string unchanged
        assertEquals(input, result);
    }

    @Test
    @DisplayName("invalid JSON is wrapped as plain message with empty devices")
    void invalidJson_wrappedAsMessage() throws Exception {
        String result = invoke("this is not json");
        JsonNode node = objectMapper.readTree(result);
        assertEquals("this is not json", node.get("message").asText());
        assertEquals(0, node.get("count").asInt());
        assertTrue(node.get("devices").isArray());
        assertEquals(0, node.get("devices").size());
    }

    @Test
    @DisplayName("JSON primitive (number) is wrapped as plain message")
    void jsonPrimitive_wrappedAsMessage() throws Exception {
        String result = invoke("42");
        JsonNode node = objectMapper.readTree(result);
        assertEquals("42", node.get("message").asText());
        assertEquals(0, node.get("count").asInt());
    }

    @Test
    @DisplayName("JSON primitive (string) is wrapped as plain message")
    void jsonString_wrappedAsMessage() throws Exception {
        String result = invoke("\"hello\"");
        JsonNode node = objectMapper.readTree(result);
        assertEquals("\"hello\"", node.get("message").asText());
        assertEquals(0, node.get("count").asInt());
    }

    @Test
    @DisplayName("empty JSON array returns count=0")
    void emptyArray_returnsZeroCount() throws Exception {
        String result = invoke("[]");
        JsonNode node = objectMapper.readTree(result);
        assertEquals(0, node.get("count").asInt());
        assertTrue(node.get("devices").isArray());
        assertEquals(0, node.get("devices").size());
    }
}
