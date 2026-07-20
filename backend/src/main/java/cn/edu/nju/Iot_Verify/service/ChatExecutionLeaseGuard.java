package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.exception.ConflictException;
import cn.edu.nju.Iot_Verify.po.ChatSessionPo;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import lombok.RequiredArgsConstructor;
import org.springframework.stereotype.Component;

import java.time.LocalDateTime;
import java.util.Objects;

/** Fences AI-originated writes with the chat execution lease that authorized them. */
@Component
@RequiredArgsConstructor
public class ChatExecutionLeaseGuard {

    private final ChatSessionRepository sessionRepository;

    public void requireCurrentExecutionLease() {
        String executionId = UserContextHolder.getChatExecutionId();
        if (executionId == null || executionId.isBlank()) {
            return;
        }
        Long userId = UserContextHolder.getUserId();
        String sessionId = UserContextHolder.getChatSessionId();
        if (userId == null || sessionId == null || sessionId.isBlank()) {
            throw leaseLost();
        }
        ChatSessionPo session = sessionRepository.findByIdAndUserIdForUpdate(sessionId, userId)
                .orElseThrow(this::leaseLost);
        LocalDateTime now = sessionRepository.currentDatabaseTime();
        if (!Objects.equals(executionId, session.getActiveExecutionId())
                || session.getActiveExecutionExpiresAt() == null
                || !session.getActiveExecutionExpiresAt().isAfter(now)
                || Boolean.TRUE.equals(session.getExecutionStopRequested())) {
            throw leaseLost();
        }
    }

    private ConflictException leaseLost() {
        return new ConflictException(
                "The assistant execution no longer owns this session. No new mutation was committed.");
    }
}
