package cn.edu.nju.Iot_Verify.component.ai.model;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class LlmChatResponseTest {

    @Test
    void textAndToolCalls_canCoexistForReactSummaries() {
        LlmToolCall call = new LlmToolCall("call_1", "board_overview", "{}");

        LlmChatResponse response = LlmChatResponse.ofTextAndToolCalls(
                "Inspect the current board before choosing a mutation.", List.of(call));

        assertEquals("Inspect the current board before choosing a mutation.", response.text());
        assertEquals(List.of(call), response.toolCalls());
        assertTrue(response.hasToolCalls());
    }
}
