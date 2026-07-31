package cn.edu.nju.Iot_Verify.dto.chat;

import cn.edu.nju.Iot_Verify.component.ai.model.ChatExecutionStatus;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ChatSessionResponseDtoTest {

    @Test
    void serializesPersistentResultVisibilityWithTheFrontendFieldNames() {
        ChatSessionResponseDto session = new ChatSessionResponseDto();
        session.setLatestTerminalMessageId(42L);
        session.setLatestExecutionStatus(ChatExecutionStatus.FAILED);
        session.setHasUnreadUpdate(true);

        JsonNode json = new ObjectMapper().valueToTree(session);

        assertEquals(42L, json.path("latestTerminalMessageId").asLong());
        assertEquals("FAILED", json.path("latestExecutionStatus").asText());
        assertTrue(json.path("hasUnreadUpdate").asBoolean());
    }
}
