package cn.edu.nju.Iot_Verify.component.ai.state;

import cn.edu.nju.Iot_Verify.po.AiSessionStatePo;
import cn.edu.nju.Iot_Verify.repository.AiSessionStateRepository;
import cn.edu.nju.Iot_Verify.service.ChatExecutionLeaseGuard;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.dao.DataIntegrityViolationException;
import org.springframework.dao.OptimisticLockingFailureException;
import org.springframework.scheduling.annotation.Scheduled;
import org.springframework.stereotype.Component;
import org.springframework.transaction.TransactionDefinition;
import org.springframework.transaction.support.TransactionTemplate;

import java.time.Instant;
import java.util.Optional;

/** Database-backed AI session state with periodic expiry cleanup and optimistic consumption. */
@Slf4j
@Component
@RequiredArgsConstructor
public class JpaAiSessionStateStore implements AiSessionStateStore {

    private static final int WRITE_ATTEMPTS = 3;

    private final AiSessionStateRepository repository;
    private final ObjectMapper objectMapper;
    private final ChatExecutionLeaseGuard chatExecutionLeaseGuard;
    private final TransactionTemplate transactionTemplate;

    @Override
    public Optional<Snapshot> get(Long userId, String sessionId, Kind kind, Instant now) {
        String stateKey = stateKey(userId, sessionId, kind);
        AiSessionStatePo state = repository.findById(stateKey).orElse(null);
        if (state == null) return Optional.empty();
        long version = state.getVersion() == null ? 0L : state.getVersion();
        if (!state.getExpiresAt().isAfter(now)) {
            repository.deleteByStateKeyAndVersion(stateKey, version);
            return Optional.empty();
        }
        try {
            return Optional.of(new Snapshot(
                    objectMapper.readTree(state.getPayloadJson()),
                    state.getExpiresAt(),
                    version));
        } catch (Exception e) {
            repository.deleteByStateKeyAndVersion(stateKey, version);
            log.error("Removed unreadable AI session state: key={}, kind={}", stateKey, kind, e);
            return Optional.empty();
        }
    }

    @Override
    public void put(Long userId, String sessionId, Kind kind, JsonNode payload, Instant expiresAt) {
        String stateKey = stateKey(userId, sessionId, kind);
        String payloadJson;
        try {
            payloadJson = objectMapper.writeValueAsString(payload);
        } catch (Exception e) {
            throw new IllegalStateException("Could not serialize AI session state", e);
        }

        RuntimeException lastFailure = null;
        for (int attempt = 0; attempt < WRITE_ATTEMPTS; attempt++) {
            try {
                transactionTemplate.executeWithoutResult(status -> {
                    requireCurrentExecutionLease();
                    AiSessionStatePo state = repository.findById(stateKey).orElseGet(AiSessionStatePo::new);
                    state.setStateKey(stateKey);
                    state.setUserId(userId);
                    state.setSessionId(sessionId);
                    state.setStateKind(kind);
                    state.setPayloadJson(payloadJson);
                    state.setExpiresAt(expiresAt);
                    repository.saveAndFlush(state);
                });
                return;
            } catch (OptimisticLockingFailureException | DataIntegrityViolationException e) {
                lastFailure = e;
            }
        }
        throw new IllegalStateException("Could not update concurrent AI session state", lastFailure);
    }

    @Override
    public boolean remove(Long userId, String sessionId, Kind kind, long expectedVersion) {
        return Boolean.TRUE.equals(transactionTemplate.execute(status -> {
            requireCurrentExecutionLease();
            return repository.deleteByStateKeyAndVersion(
                    stateKey(userId, sessionId, kind), expectedVersion) == 1;
        }));
    }

    @Override
    public void remove(Long userId, String sessionId, Kind kind) {
        transactionTemplate.executeWithoutResult(status -> {
            requireCurrentExecutionLease();
            repository.deleteState(userId, requireSession(sessionId), requireKind(kind));
        });
    }

    @Override
    public void removeSession(Long userId, String sessionId) {
        transactionTemplate.executeWithoutResult(status -> {
            requireCurrentExecutionLease();
            repository.deleteSession(requireUser(userId), requireSession(sessionId));
        });
    }

    @Override
    public void removeUser(Long userId) {
        TransactionTemplate independentTransaction = new TransactionTemplate(
                transactionTemplate.getTransactionManager());
        independentTransaction.setPropagationBehavior(TransactionDefinition.PROPAGATION_REQUIRES_NEW);
        independentTransaction.executeWithoutResult(status -> {
            requireCurrentExecutionLease();
            repository.deleteUser(requireUser(userId));
        });
    }

    @Scheduled(fixedDelayString = "${iot-verify.ai.session-state-cleanup-ms:60000}")
    public void purgeExpired() {
        int removed = repository.deleteExpired(Instant.now());
        if (removed > 0) {
            log.debug("Purged {} expired AI session state row(s)", removed);
        }
    }

    private String stateKey(Long userId, String sessionId, Kind kind) {
        return requireKind(kind).name() + ":" + requireUser(userId) + ":" + requireSession(sessionId);
    }

    private void requireCurrentExecutionLease() {
        chatExecutionLeaseGuard.requireCurrentExecutionLease();
    }

    private Long requireUser(Long userId) {
        if (userId == null) throw new IllegalArgumentException("AI session state requires a user.");
        return userId;
    }

    private String requireSession(String sessionId) {
        if (sessionId == null || sessionId.isBlank()) {
            throw new IllegalArgumentException("AI session state requires a session.");
        }
        return sessionId;
    }

    private Kind requireKind(Kind kind) {
        if (kind == null) throw new IllegalArgumentException("AI session state requires a kind.");
        return kind;
    }
}
