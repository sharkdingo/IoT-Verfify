package cn.edu.nju.Iot_Verify.component.ai;

import cn.edu.nju.Iot_Verify.component.ai.model.LlmMessage;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmRole;
import cn.edu.nju.Iot_Verify.component.ai.model.LlmToolCall;
import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Verifies the persisted-content ⇄ domain-model conversion previously covered by the
 * ArkAiClient parsing tests, now owned by {@link LlmMessageCodec} and expressed in
 * vendor-neutral {@link LlmMessage} terms.
 */
class LlmMessageCodecTest {

    private final ObjectMapper objectMapper = new ObjectMapper();
    private final LlmMessageCodec codec = new LlmMessageCodec(objectMapper);

    @Test
    void toMessages_shouldParseStructuredToolResult() {
        ChatMessagePo po = new ChatMessagePo();
        po.setRole("tool");
        po.setContent("{\"type\":\"tool_result\",\"toolCallId\":\"tc_1\",\"result\":\"ok\"}");

        List<LlmMessage> messages = codec.toMessages(List.of(po));

        assertEquals(1, messages.size());
        LlmMessage toolMsg = messages.get(0);
        assertEquals(LlmRole.TOOL, toolMsg.role());
        assertEquals("tc_1", toolMsg.toolCallId());
        assertEquals("ok", toolMsg.content());
    }

    @Test
    void toMessages_shouldParseStructuredAssistantToolCalls() throws Exception {
        String content = objectMapper.writeValueAsString(Map.of(
                "type", LlmMessageCodec.TOOL_CALLS_JSON_TYPE,
                "toolCalls", List.of(Map.of(
                        "id", "call_1",
                        "type", "function",
                        "function", Map.of("name", "search_devices", "arguments", "{}")))));

        ChatMessagePo po = new ChatMessagePo();
        po.setRole("assistant");
        po.setContent(content);

        List<LlmMessage> messages = codec.toMessages(List.of(po));

        assertEquals(1, messages.size());
        LlmMessage assistantMsg = messages.get(0);
        assertEquals(LlmRole.ASSISTANT, assistantMsg.role());
        assertTrue(assistantMsg.hasToolCalls());
        assertEquals(1, assistantMsg.toolCalls().size());
        assertEquals("search_devices", assistantMsg.toolCalls().get(0).name());
    }

    @Test
    void toMessages_shouldParseStructuredToolResultWithLeadingWhitespace() {
        ChatMessagePo po = new ChatMessagePo();
        po.setRole("tool");
        po.setContent("  \n {\"type\":\"tool_result\",\"toolCallId\":\"tc_2\",\"result\":\"done\"}");

        List<LlmMessage> messages = codec.toMessages(List.of(po));

        assertEquals(1, messages.size());
        LlmMessage toolMsg = messages.get(0);
        assertEquals(LlmRole.TOOL, toolMsg.role());
        assertEquals("tc_2", toolMsg.toolCallId());
        assertEquals("done", toolMsg.content());
    }

    @Test
    void toMessages_shouldParseAssistantToolCallsWithLeadingWhitespace() throws Exception {
        String content = "  " + objectMapper.writeValueAsString(Map.of(
                "type", LlmMessageCodec.TOOL_CALLS_JSON_TYPE,
                "toolCalls", List.of(Map.of(
                        "id", "call_2",
                        "type", "function",
                        "function", Map.of("name", "list_devices", "arguments", "{}")))));

        ChatMessagePo po = new ChatMessagePo();
        po.setRole("assistant");
        po.setContent(content);

        List<LlmMessage> messages = codec.toMessages(List.of(po));

        assertEquals(1, messages.size());
        LlmMessage assistantMsg = messages.get(0);
        assertEquals(LlmRole.ASSISTANT, assistantMsg.role());
        assertTrue(assistantMsg.hasToolCalls());
        assertEquals("list_devices", assistantMsg.toolCalls().get(0).name());
    }

    @Test
    void toMessages_shouldParseLegacySeparatorToolResult() {
        ChatMessagePo po = new ChatMessagePo();
        po.setRole("tool");
        po.setContent("tc_legacy" + LlmMessageCodec.TOOL_RESULT_SEPARATOR + "legacy-result");

        List<LlmMessage> messages = codec.toMessages(List.of(po));

        LlmMessage toolMsg = messages.get(0);
        assertEquals("tc_legacy", toolMsg.toolCallId());
        assertEquals("legacy-result", toolMsg.content());
    }

    @Test
    void roundTrip_serializeThenParseToolCalls() {
        String serialized = codec.serializeToolCalls(List.of(new LlmToolCall("id_9", "add_device", "{\"x\":1}")));

        ChatMessagePo po = new ChatMessagePo();
        po.setRole("assistant");
        po.setContent(serialized);

        LlmMessage msg = codec.toMessages(List.of(po)).get(0);
        assertTrue(msg.hasToolCalls());
        assertEquals("id_9", msg.toolCalls().get(0).id());
        assertEquals("add_device", msg.toolCalls().get(0).name());
        assertEquals("{\"x\":1}", msg.toolCalls().get(0).argumentsJson());
    }
}
