package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import cn.edu.nju.Iot_Verify.service.ChatExecutionLeaseGuard;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.jdbc.AutoConfigureTestDatabase;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;

import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

@DataJpaTest(properties = {
        "spring.jpa.database-platform=org.hibernate.dialect.H2Dialect",
        "spring.jpa.properties.hibernate.dialect=org.hibernate.dialect.H2Dialect",
        "spring.jpa.hibernate.ddl-auto=create-drop"
})
@AutoConfigureTestDatabase(replace = AutoConfigureTestDatabase.Replace.ANY)
class ChatSessionRepositoryTest {

    @Autowired
    private ChatSessionRepository repository;

    @Test
    void leaseMaintenanceRenewsOnlyTheCurrentOwnerAndClearsOnlyExpiredRows() {
        LocalDateTime now = repository.currentDatabaseTime();
        assertTrue(now.isAfter(LocalDateTime.now().minusMinutes(1)));
        repository.saveAndFlush(session("live", "live-execution", now.plusSeconds(20)));
        repository.saveAndFlush(session("expired", "expired-execution", now.minusSeconds(1)));

        assertEquals(0, repository.renewActiveExecutionLease(
                "live", 1L, "wrong-execution", now, now.plusMinutes(1)));
        assertEquals(1, repository.renewActiveExecutionLease(
                "live", 1L, "live-execution", now, now.plusMinutes(1)));
        assertEquals(0, repository.renewActiveExecutionLease(
                "expired", 1L, "expired-execution", now, now.plusMinutes(1)));
        assertEquals(1, repository.clearExpiredExecutionLeases(now));

        ChatSessionPo live = repository.findById("live").orElseThrow();
        ChatSessionPo expired = repository.findById("expired").orElseThrow();
        assertEquals("live-execution", live.getActiveExecutionId());
        assertTrue(live.getActiveExecutionExpiresAt().isAfter(now.plusSeconds(30)));
        assertTrue(Boolean.TRUE.equals(live.getExecutionStopRequested()));
        assertNull(expired.getActiveExecutionId());
        assertNull(expired.getActiveExecutionExpiresAt());
        assertFalse(Boolean.TRUE.equals(expired.getExecutionStopRequested()));
        assertFalse(Boolean.TRUE.equals(expired.getExecutionUserStopRequested()));
    }

    @Test
    void executionLeaseGuardRejectsWritesAfterTheSessionOwnerChanges() {
        LocalDateTime now = repository.currentDatabaseTime();
        ChatSessionPo session = session("guarded", "current-execution", now.plusMinutes(1));
        session.setExecutionStopRequested(false);
        session.setExecutionUserStopRequested(false);
        repository.saveAndFlush(session);
        ChatExecutionLeaseGuard guard = new ChatExecutionLeaseGuard(repository);

        UserContextHolder.setUserId(1L);
        UserContextHolder.setChatSessionId("guarded");
        UserContextHolder.setChatExecutionId("current-execution");
        try {
            assertDoesNotThrow(guard::requireCurrentExecutionLease);

            session.setActiveExecutionId("replacement-execution");
            repository.saveAndFlush(session);

            assertThrows(ConflictException.class, guard::requireCurrentExecutionLease);
        } finally {
            UserContextHolder.clear();
        }
    }

    private ChatSessionPo session(String id, String executionId, LocalDateTime expiresAt) {
        ChatSessionPo session = new ChatSessionPo();
        session.setId(id);
        session.setUserId(1L);
        session.setActiveExecutionId(executionId);
        session.setActiveExecutionExpiresAt(expiresAt);
        session.setExecutionStopRequested(true);
        session.setExecutionUserStopRequested(true);
        return session;
    }
}
