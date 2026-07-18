package cn.edu.nju.Iot_Verify.component.aitool.scenario;

import cn.edu.nju.Iot_Verify.dto.board.BoardReplacementPreviewDto;
import com.fasterxml.jackson.databind.JsonNode;
import org.springframework.stereotype.Component;

import java.time.Clock;
import java.time.Duration;
import java.time.Instant;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.ConcurrentMap;

/**
 * Server-side lifecycle for the latest chat-generated scene draft.
 *
 * <p>The draft and its replacement preview deliberately live outside the LLM history. A scene
 * can be much larger than the chat context window, and a confirmation must never depend on the
 * model copying the scene or an impact token back from a truncated tool result.</p>
 */
@Component
public class AiScenarioDraftStore {

    static final Duration DRAFT_TTL = Duration.ofHours(1);
    static final Duration PENDING_TTL = Duration.ofMinutes(15);

    private final ConcurrentMap<SessionScope, Entry> entries = new ConcurrentHashMap<>();
    private final Clock clock;

    public AiScenarioDraftStore() {
        this(Clock.systemUTC());
    }

    AiScenarioDraftStore(Clock clock) {
        this.clock = clock;
    }

    public void saveDraft(Long userId, String sessionId, String scenarioName, JsonNode scene) {
        SessionScope scope = scope(userId, sessionId);
        if (scene == null || !scene.isObject() || !scene.path("devices").isArray()
                || scene.path("devices").isEmpty()) {
            return;
        }
        Instant now = clock.instant();
        entries.put(scope, new Entry(
                scenarioName == null || scenarioName.isBlank() ? "AI Scenario" : scenarioName,
                scene.deepCopy(),
                now.plus(DRAFT_TTL),
                null,
                null));
    }

    public void clearDraft(Long userId, String sessionId) {
        entries.remove(scope(userId, sessionId));
    }

    public void clearPendingApplication(Long userId, String sessionId) {
        SessionScope scope = scope(userId, sessionId);
        Entry entry = active(scope);
        if (entry != null && entry.pendingPreview() != null) {
            entries.put(scope, entry.withPending(null, null));
        }
    }

    public Optional<DraftSnapshot> latestDraft(Long userId, String sessionId) {
        Entry entry = active(scope(userId, sessionId));
        if (entry == null) return Optional.empty();
        return Optional.of(new DraftSnapshot(entry.scenarioName(), entry.scene().deepCopy()));
    }

    public Optional<PendingApplication> beginApplication(Long userId,
                                                          String sessionId,
                                                          BoardReplacementPreviewDto preview) {
        SessionScope scope = scope(userId, sessionId);
        Entry entry = active(scope);
        if (entry == null || preview == null) return Optional.empty();
        Instant expiresAt = clock.instant().plus(PENDING_TTL);
        Entry pending = entry.withPending(copyPreview(preview), expiresAt);
        entries.put(scope, pending);
        return Optional.of(toPending(pending));
    }

    public Optional<PendingApplication> pendingApplication(Long userId, String sessionId) {
        Entry entry = active(scope(userId, sessionId));
        if (entry == null || entry.pendingPreview() == null || entry.pendingExpiresAt() == null) {
            return Optional.empty();
        }
        if (!entry.pendingExpiresAt().isAfter(clock.instant())) {
            entries.computeIfPresent(scope(userId, sessionId), (ignored, current) ->
                    current.withPending(null, null));
            return Optional.empty();
        }
        return Optional.of(toPending(entry));
    }

    public Optional<PendingApplication> refreshPendingApplication(Long userId,
                                                                   String sessionId,
                                                                   BoardReplacementPreviewDto preview) {
        SessionScope scope = scope(userId, sessionId);
        Entry entry = active(scope);
        if (entry == null || entry.pendingPreview() == null || preview == null) return Optional.empty();
        Entry refreshed = entry.withPending(copyPreview(preview), clock.instant().plus(PENDING_TTL));
        entries.put(scope, refreshed);
        return Optional.of(toPending(refreshed));
    }

    public void completeApplication(Long userId, String sessionId) {
        entries.remove(scope(userId, sessionId));
    }

    public void clearSession(String sessionId) {
        if (sessionId == null || sessionId.isBlank()) return;
        entries.keySet().removeIf(scope -> scope.sessionId().equals(sessionId));
    }

    public void clearUser(Long userId) {
        if (userId == null) return;
        entries.keySet().removeIf(scope -> scope.userId().equals(userId));
    }

    private Entry active(SessionScope scope) {
        Entry entry = entries.get(scope);
        if (entry == null) return null;
        if (!entry.draftExpiresAt().isAfter(clock.instant())) {
            entries.remove(scope, entry);
            return null;
        }
        return entry;
    }

    private PendingApplication toPending(Entry entry) {
        return new PendingApplication(
                entry.scenarioName(),
                entry.scene().deepCopy(),
                copyPreview(entry.pendingPreview()),
                entry.pendingExpiresAt());
    }

    private BoardReplacementPreviewDto copyPreview(BoardReplacementPreviewDto source) {
        if (source == null) return null;
        return BoardReplacementPreviewDto.builder()
                .impactToken(source.getImpactToken())
                .deviceCount(source.getDeviceCount())
                .environmentVariableCount(source.getEnvironmentVariableCount())
                .ruleCount(source.getRuleCount())
                .specificationCount(source.getSpecificationCount())
                .build();
    }

    private SessionScope scope(Long userId, String sessionId) {
        if (userId == null || sessionId == null || sessionId.isBlank()) {
            throw new IllegalArgumentException("A chat user and session are required for a scenario draft.");
        }
        return new SessionScope(userId, sessionId);
    }

    public record DraftSnapshot(String scenarioName, JsonNode scene) {
    }

    public record PendingApplication(String scenarioName,
                                     JsonNode scene,
                                     BoardReplacementPreviewDto preview,
                                     Instant expiresAt) {
    }

    private record SessionScope(Long userId, String sessionId) {
    }

    private record Entry(String scenarioName,
                         JsonNode scene,
                         Instant draftExpiresAt,
                         BoardReplacementPreviewDto pendingPreview,
                         Instant pendingExpiresAt) {
        private Entry withPending(BoardReplacementPreviewDto preview, Instant expiresAt) {
            return new Entry(scenarioName, scene, draftExpiresAt, preview, expiresAt);
        }
    }
}
