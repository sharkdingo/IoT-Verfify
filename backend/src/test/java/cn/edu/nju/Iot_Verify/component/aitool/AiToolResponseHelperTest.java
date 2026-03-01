package cn.edu.nju.Iot_Verify.component.aitool;

import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

class AiToolResponseHelperTest {

    @Test
    void success_whenSerializationSucceeds_shouldReturnBodyJson() throws Exception {
        ObjectMapper mapper = new ObjectMapper();

        String result = AiToolResponseHelper.success(
                mapper,
                Map.of("message", "ok", "taskId", 9L),
                "fallback message");

        JsonNode json = mapper.readTree(result);
        assertEquals("ok", json.path("message").asText());
        assertEquals(9L, json.path("taskId").asLong());
    }

    @Test
    void success_whenSerializationFails_shouldReturnFallbackSuccessJson() throws Exception {
        ObjectMapper failingMapper = mock(ObjectMapper.class);
        when(failingMapper.writeValueAsString(any())).thenThrow(new JsonProcessingException("boom") {
        });

        String result = AiToolResponseHelper.success(
                failingMapper,
                Map.of("message", "ok"),
                "Operation accepted.");

        JsonNode json = new ObjectMapper().readTree(result);
        assertEquals("Operation accepted.", json.path("message").asText());
        assertTrue(json.path("warning").asText().contains("serialization degraded"));
    }
}
