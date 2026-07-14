package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

class ChatMapperTest {

    private final ChatMapper mapper = new ChatMapper();

    @Test
    void toChatSessionDto_hidesInternalUntitledPlaceholders() {
        ChatSessionPo current = new ChatSessionPo();
        current.setId("current");
        current.setTitle(null);
        ChatSessionPo legacy = new ChatSessionPo();
        legacy.setId("legacy");
        legacy.setTitle("New Chat");

        assertNull(mapper.toChatSessionDto(current).getTitle());
        assertNull(mapper.toChatSessionDto(legacy).getTitle());
    }

    @Test
    void toChatSessionDto_preservesUserDerivedTitle() {
        ChatSessionPo session = new ChatSessionPo();
        session.setId("named");
        session.setTitle("玄关安全检查");

        assertEquals("玄关安全检查", mapper.toChatSessionDto(session).getTitle());
    }
}
