package cn.edu.nju.Iot_Verify.repository;

import cn.edu.nju.Iot_Verify.po.ChatMessagePo;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import org.junit.jupiter.api.Test;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.boot.test.autoconfigure.jdbc.AutoConfigureTestDatabase;
import org.springframework.boot.test.autoconfigure.orm.jpa.DataJpaTest;
import org.springframework.dao.DataIntegrityViolationException;
import org.springframework.transaction.PlatformTransactionManager;
import org.springframework.transaction.annotation.Propagation;
import org.springframework.transaction.annotation.Transactional;
import org.springframework.transaction.support.TransactionTemplate;

import java.time.LocalDateTime;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
class ChatMessageRepositoryTest {

    @Autowired
    private ChatMessageRepository messageRepository;

    @Autowired
    private ChatSessionRepository sessionRepository;

    @Autowired
    private PlatformTransactionManager transactionManager;

    @Test
    void turnRoleConstraintRejectsASecondVisibleMessage() {
        messageRepository.saveAndFlush(message("session-1", "turn-1", "user", "execution-1"));

        assertThrows(DataIntegrityViolationException.class, () ->
                messageRepository.saveAndFlush(
                        message("session-1", "turn-1", "user", "execution-2")));
    }

    @Test
    void oneUserAndOneTerminalAssistantMayShareATurn() {
        messageRepository.saveAndFlush(message("session-2", "turn-1", "user", "execution-1"));
        messageRepository.saveAndFlush(message("session-2", "turn-1", "assistant", "execution-1"));

        assertEquals(2, messageRepository.countBySessionId("session-2"));
    }

    @Test
    void internalMessagesWithNullTurnIdsRemainRepeatable() {
        messageRepository.saveAndFlush(message("session-3", null, "assistant", "execution-1"));
        messageRepository.saveAndFlush(message("session-3", null, "assistant", "execution-1"));
        messageRepository.saveAndFlush(message("session-3", null, "tool", "execution-1"));
        messageRepository.saveAndFlush(message("session-3", null, "tool", "execution-1"));

        assertEquals(4, messageRepository.countBySessionId("session-3"));
    }

    @Test
    void exactExecutionDeleteCannotRemoveAnotherTurnOrRole() {
        messageRepository.saveAndFlush(message("session-4", "turn-1", "user", "execution-1"));
        messageRepository.saveAndFlush(message("session-4", "turn-1", "assistant", "execution-1"));
        messageRepository.saveAndFlush(message("session-4", "turn-2", "user", "execution-2"));

        assertEquals(0, messageRepository.deleteBySessionIdAndTurnIdAndExecutionIdAndRole(
                "session-4", "turn-1", "wrong-execution", "user"));
        assertEquals(1, messageRepository.deleteBySessionIdAndTurnIdAndExecutionIdAndRole(
                "session-4", "turn-1", "execution-1", "user"));

        assertFalse(messageRepository.existsBySessionIdAndTurnIdAndExecutionIdAndRole(
                "session-4", "turn-1", "execution-1", "user"));
        assertTrue(messageRepository.existsBySessionIdAndTurnIdAndExecutionIdAndRole(
                "session-4", "turn-1", "execution-1", "assistant"));
        assertTrue(messageRepository.existsBySessionIdAndTurnIdAndExecutionIdAndRole(
                "session-4", "turn-2", "execution-2", "user"));
    }

    @Test
    @Transactional(propagation = Propagation.NOT_SUPPORTED)
    void leaseAndAdmittedUserTurnRollBackInOneTransaction() {
        TransactionTemplate transaction = new TransactionTemplate(transactionManager);
        transaction.executeWithoutResult(status -> {
            ChatSessionPo session = new ChatSessionPo();
            session.setId("session-atomic");
            session.setUserId(7L);
            session.setTitle("New Chat");
            sessionRepository.saveAndFlush(session);
        });

        assertThrows(IllegalStateException.class, () -> transaction.executeWithoutResult(status -> {
            ChatSessionPo session = sessionRepository.findById("session-atomic").orElseThrow();
            session.setActiveExecutionId("execution-atomic");
            session.setActiveExecutionExpiresAt(LocalDateTime.now().plusMinutes(1));
            sessionRepository.saveAndFlush(session);
            messageRepository.saveAndFlush(
                    message("session-atomic", "turn-atomic", "user", "execution-atomic"));
            throw new IllegalStateException("force admission rollback");
        }));

        transaction.executeWithoutResult(status -> {
            ChatSessionPo session = sessionRepository.findById("session-atomic").orElseThrow();
            assertNull(session.getActiveExecutionId());
            assertNull(session.getActiveExecutionExpiresAt());
            assertFalse(messageRepository.existsBySessionIdAndTurnIdAndExecutionIdAndRole(
                    "session-atomic", "turn-atomic", "execution-atomic", "user"));
        });
    }

    private ChatMessagePo message(
            String sessionId, String turnId, String role, String executionId) {
        ChatMessagePo message = new ChatMessagePo();
        message.setSessionId(sessionId);
        message.setTurnId(turnId);
        message.setRole(role);
        message.setExecutionId(executionId);
        message.setContent(role + " content");
        return message;
    }
}
