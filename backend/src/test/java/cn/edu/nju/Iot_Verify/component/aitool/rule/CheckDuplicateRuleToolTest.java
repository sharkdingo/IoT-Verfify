package cn.edu.nju.Iot_Verify.component.aitool.rule;

import cn.edu.nju.Iot_Verify.component.ai.PromptCompletionService;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.BoardStorageService;
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
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.anyDouble;
import static org.mockito.ArgumentMatchers.anyInt;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.never;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

@ExtendWith(MockitoExtension.class)
class CheckDuplicateRuleToolTest {

    @Mock
    private BoardStorageService boardStorageService;

    @Mock
    private PromptCompletionService promptCompletionService;

    private CheckDuplicateRuleTool tool;

    @BeforeEach
    void setUp() {
        tool = new CheckDuplicateRuleTool(boardStorageService, promptCompletionService, new ObjectMapper());
        UserContextHolder.setUserId(1L);
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    /**
     * Regression: the "no existing rules" branch used to build its response with
     * {@code Map.of(..., "duplicateWith", null, ...)}, which throws NPE (Map.of forbids
     * null values). That NPE was swallowed by the catch-all and returned as a 500
     * INTERNAL_ERROR, so checking the very first rule on an empty board failed instead of
     * returning {isDuplicate:false}. This asserts the branch now returns clean JSON.
     */
    @Test
    void checkDuplicate_whenNoExistingRules_returnsNotDuplicateWithoutError() throws Exception {
        when(boardStorageService.getRules(anyLong())).thenReturn(List.of());

        String argsJson = """
                {
                  "newRule":{
                    "conditions":[
                      {"deviceName":"Light_1","attribute":"state","relation":"=","value":"On"}
                    ],
                    "command":{"deviceName":"Light_1","action":"turnOn"}
                  }
                }
                """;

        String result = tool.execute(argsJson);
        JsonNode json = new ObjectMapper().readTree(result);

        // No error envelope produced (NPE would have surfaced as INTERNAL_ERROR/500).
        assertTrue(json.path("error").isMissingNode(), "unexpected error envelope: " + result);
        assertFalse(json.path("isDuplicate").asBoolean(true), "first rule on empty board must not be duplicate");
        assertEquals(0.0, json.path("similarity").asDouble(-1.0));
        assertTrue(json.path("duplicateWith").isNull(), "duplicateWith should be JSON null");
        assertTrue(json.path("message").asText().contains("first rule"));

        // The LLM must not be consulted when there is nothing to compare against.
        verify(promptCompletionService, never())
                .complete(anyString(), anyString(), anyDouble(), anyInt());
    }
}
