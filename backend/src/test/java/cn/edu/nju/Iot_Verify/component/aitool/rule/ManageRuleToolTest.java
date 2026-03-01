package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
import com.fasterxml.jackson.core.JsonProcessingException;
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
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.Mockito.doThrow;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.spy;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class ManageRuleToolTest {

    @Mock
    private BoardStorageService boardStorageService;

    private ManageRuleTool tool;

    @BeforeEach
    void setUp() {
        tool = new ManageRuleTool(boardStorageService, new ObjectMapper());
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void add_withUnsupportedRelation_shouldReject() {
        String argsJson = """
                {
                  "action":"add",
                  "conditions":[
                    {
                      "deviceName":"Light_1",
                      "attribute":"state",
                      "relation":"approx",
                      "value":"On"
                    }
                  ],
                  "command":{
                    "deviceName":"Light_1",
                    "action":"turnOn"
                  }
                }
                """;

        String result = tool.execute(argsJson);

        assertTrue(result.contains("Unsupported relation"));
        verify(boardStorageService, never()).saveRules(anyLong(), any());
    }

    @Test
    void execute_whenJsonSerializationFails_shouldReturnStableErrorJson() throws Exception {
        ObjectMapper failingMapper = mock(ObjectMapper.class);
        when(failingMapper.writeValueAsString(any())).thenThrow(new JsonProcessingException("boom") {
        });

        ManageRuleTool fallbackTool = new ManageRuleTool(boardStorageService, failingMapper);
        UserContextHolder.clear();

        String result = fallbackTool.execute("{}");

        JsonNode json = new ObjectMapper().readTree(result);
        assertEquals("User not logged in", json.path("error").asText());
        assertEquals("UNAUTHORIZED", json.path("errorCode").asText());
        assertEquals(401, json.path("status").asInt());
    }

    @Test
    void add_whenResponseSerializationFails_shouldReturnFallbackSuccess() throws Exception {
        ObjectMapper failingMapper = spy(new ObjectMapper());
        doThrow(new RuntimeException("boom")).when(failingMapper).writeValueAsString(any());

        when(boardStorageService.getRules(1L)).thenReturn(List.of());
        when(boardStorageService.saveRules(anyLong(), any())).thenReturn(List.of());

        ManageRuleTool fallbackTool = new ManageRuleTool(boardStorageService, failingMapper);

        String argsJson = """
                {
                  "action":"add",
                  "conditions":[
                    {
                      "deviceName":"Light_1",
                      "attribute":"state",
                      "relation":"=",
                      "value":"On"
                    }
                  ],
                  "command":{
                    "deviceName":"Light_1",
                    "action":"turnOn"
                  }
                }
                """;

        String result = fallbackTool.execute(argsJson);
        JsonNode json = new ObjectMapper().readTree(result);

        assertEquals("Rule added successfully.", json.path("message").asText());
        assertTrue(json.path("warning").asText().contains("serialization degraded"));
    }
}
