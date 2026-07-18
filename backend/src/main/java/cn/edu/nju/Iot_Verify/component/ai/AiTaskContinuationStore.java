package cn.edu.nju.Iot_Verify.component.ai;

import org.springframework.stereotype.Component;

import java.time.Clock;
import java.time.Duration;
import java.time.Instant;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

/** Keeps user-authored task context across a server-enforced confirmation pause. */
@Component
public class AiTaskContinuationStore {

    static final Duration CONTINUATION_TTL = Duration.ofMinutes(15);
    static final int MAX_OBJECTIVE_CHARS = 4000;
    static final int MAX_UPDATE_CHARS = 1000;
    static final int MAX_UPDATES = 4;
    static final int MAX_PENDING_RESULT_CHARS = 3000;

    private final ConcurrentMap<SessionScope, PendingTask> pendingBySession = new ConcurrentHashMap<>();
    private final Clock clock;

    public AiTaskContinuationStore() {
        this(Clock.systemUTC());
    }

    AiTaskContinuationStore(Clock clock) {
        this.clock = clock;
    }

    public void save(Long userId, String sessionId, String objective) {
        savePendingStep(userId, sessionId, objective, objective, null, null);
    }

    public void savePendingStep(Long userId,
                                String sessionId,
                                String fallbackObjective,
                                String latestUserMessage,
                                String pendingToolName,
                                String pendingResult) {
        SessionScope scope = scope(userId, sessionId);
        PendingTask current = active(scope);
        String objective = current == null
                ? boundedText(fallbackObjective, MAX_OBJECTIVE_CHARS)
                : current.originalObjective();
        if (objective == null) {
            pendingBySession.remove(scope);
            return;
        }

        List<String> updates = current == null
                ? new ArrayList<>()
                : new ArrayList<>(current.recentUserMessages());
        addUpdate(updates, objective, latestUserMessage);
        pendingBySession.put(scope, new PendingTask(
                objective,
                List.copyOf(updates),
                boundedText(pendingToolName, 120),
                boundedText(pendingResult, MAX_PENDING_RESULT_CHARS),
                clock.instant().plus(CONTINUATION_TTL)));
    }

    public void rememberUserMessage(Long userId, String sessionId, String userMessage) {
        SessionScope scope = scope(userId, sessionId);
        PendingTask current = active(scope);
        if (current == null) return;
        List<String> updates = new ArrayList<>(current.recentUserMessages());
        addUpdate(updates, current.originalObjective(), userMessage);
        pendingBySession.put(scope, new PendingTask(
                current.originalObjective(),
                List.copyOf(updates),
                current.pendingToolName(),
                current.pendingResult(),
                clock.instant().plus(CONTINUATION_TTL)));
    }

    public Optional<ContinuationContext> pendingContext(Long userId, String sessionId) {
        PendingTask pending = active(scope(userId, sessionId));
        if (pending == null) return Optional.empty();
        return Optional.of(new ContinuationContext(
                pending.originalObjective(),
                List.copyOf(pending.recentUserMessages()),
                pending.pendingToolName(),
                pending.pendingResult(),
                pending.expiresAt()));
    }

    public Optional<String> pendingObjective(Long userId, String sessionId) {
        return pendingContext(userId, sessionId).map(ContinuationContext::originalObjective);
    }

    public void clear(Long userId, String sessionId) {
        pendingBySession.remove(scope(userId, sessionId));
    }

    public void clearSession(String sessionId) {
        if (sessionId == null || sessionId.isBlank()) return;
        pendingBySession.keySet().removeIf(scope -> scope.sessionId().equals(sessionId));
    }

    public void clearUser(Long userId) {
        if (userId == null) return;
        pendingBySession.keySet().removeIf(scope -> scope.userId().equals(userId));
    }

    private PendingTask active(SessionScope scope) {
        PendingTask pending = pendingBySession.get(scope);
        if (pending == null) return null;
        if (!pending.expiresAt().isAfter(clock.instant())) {
            pendingBySession.remove(scope, pending);
            return null;
        }
        return pending;
    }

    private void addUpdate(List<String> updates, String objective, String value) {
        String update = boundedText(value, MAX_UPDATE_CHARS);
        if (update == null || update.equals(objective)
                || (!updates.isEmpty() && update.equals(updates.get(updates.size() - 1)))) {
            return;
        }
        updates.add(update);
        while (updates.size() > MAX_UPDATES) {
            updates.remove(0);
        }
    }

    private String boundedText(String value, int maxChars) {
        if (value == null) return null;
        String normalized = value.trim();
        if (normalized.isEmpty()) return null;
        return normalized.length() <= maxChars ? normalized : normalized.substring(0, maxChars);
    }

    private SessionScope scope(Long userId, String sessionId) {
        if (userId == null || sessionId == null || sessionId.isBlank()) {
            throw new IllegalArgumentException("A chat user and session are required for task continuation.");
        }
        return new SessionScope(userId, sessionId);
    }

    public record ContinuationContext(String originalObjective,
                                      List<String> recentUserMessages,
                                      String pendingToolName,
                                      String pendingResult,
                                      Instant expiresAt) {
    }

    private record SessionScope(Long userId, String sessionId) {
    }

    private record PendingTask(String originalObjective,
                               List<String> recentUserMessages,
                               String pendingToolName,
                               String pendingResult,
                               Instant expiresAt) {
    }
}
