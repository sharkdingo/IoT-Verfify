package cn.edu.nju.Iot_Verify.client;

import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessage;
import com.volcengine.ark.runtime.model.completion.chat.ChatMessageRole;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

class ArkAiClientMessageParsingTest {

    private final ObjectMapper objectMapper = new ObjectMapper();

    @Test
    void convertToSdkMessages_shouldParseStructuredToolResult() {
        ArkAiClient client = new ArkAiClient();

        ChatMessagePo po = new ChatMessagePo();
        po.setRole("tool");
        po.setContent("{\"type\":\"tool_result\",\"toolCallId\":\"tc_1\",\"result\":\"ok\"}");

        List<ChatMessage> messages = client.convertToSdkMessages(List.of(po));

        assertEquals(1, messages.size());
        ChatMessage toolMsg = messages.get(0);
        assertEquals(ChatMessageRole.TOOL, toolMsg.getRole());
        assertEquals("tc_1", toolMsg.getToolCallId());
        assertEquals("ok", toolMsg.getContent().toString());
    }

    @Test
    void convertToSdkMessages_shouldParseStructuredAssistantToolCalls() throws Exception {
        ArkAiClient client = new ArkAiClient();

        String content = objectMapper.writeValueAsString(Map.of(
                "type", ArkAiClient.TOOL_CALLS_JSON_TYPE,
                "toolCalls", List.of(Map.of(
                        "id", "call_1",
                        "type", "function",
                        "function", Map.of(
                                "name", "search_devices",
                                "arguments", "{}"
                        )
                ))
        ));

        ChatMessagePo po = new ChatMessagePo();
        po.setRole("assistant");
        po.setContent(content);

        List<ChatMessage> messages = client.convertToSdkMessages(List.of(po));

        assertEquals(1, messages.size());
        ChatMessage assistantMsg = messages.get(0);
        assertEquals(ChatMessageRole.ASSISTANT, assistantMsg.getRole());
        assertNotNull(assistantMsg.getToolCalls());
        assertEquals(1, assistantMsg.getToolCalls().size());
        assertEquals("search_devices", assistantMsg.getToolCalls().get(0).getFunction().getName());
    }
}
