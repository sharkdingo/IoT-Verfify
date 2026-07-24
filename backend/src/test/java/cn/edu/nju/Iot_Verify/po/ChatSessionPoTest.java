package cn.edu.nju.Iot_Verify.po;

import org.junit.jupiter.api.Test;

import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

class ChatSessionPoTest {

    @Test
    void prePersistPreservesExplicitDatabaseTimestamps() {
        LocalDateTime databaseTime = LocalDateTime.of(2026, 7, 24, 10, 15, 30);
        ChatSessionPo session = new ChatSessionPo();
        session.setCreatedAt(databaseTime);
        session.setUpdatedAt(databaseTime);

        session.onCreate();

        assertEquals(databaseTime, session.getCreatedAt());
        assertEquals(databaseTime, session.getUpdatedAt());
    }

    @Test
    void prePersistStillInitializesMissingTimestamps() {
        ChatSessionPo session = new ChatSessionPo();

        session.onCreate();

        assertNotNull(session.getCreatedAt());
        assertEquals(session.getCreatedAt(), session.getUpdatedAt());
    }
}
