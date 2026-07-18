package cn.edu.nju.Iot_Verify.component.aitool.scenario;

import cn.edu.nju.Iot_Verify.component.ai.state.AiSessionStateStore;
import cn.edu.nju.Iot_Verify.component.ai.state.InMemoryAiSessionStateStore;
import cn.edu.nju.Iot_Verify.dto.board.BoardReplacementPreviewDto;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.JsonNodeFactory;
import com.fasterxml.jackson.databind.node.ObjectNode;
import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.stereotype.Component;

import java.time.Clock;
import java.time.Duration;
import java.time.Instant;
import java.util.Optional;

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

    private final AiSessionStateStore stateStore;
    private final ObjectMapper objectMapper;
    private final Clock clock;

    public AiScenarioDraftStore() {
        this(new InMemoryAiSessionStateStore(), new ObjectMapper(), Clock.systemUTC());
    }

    @Autowired
    public AiScenarioDraftStore(AiSessionStateStore stateStore, ObjectMapper objectMapper) {
        this(stateStore, objectMapper, Clock.systemUTC());
    }

    AiScenarioDraftStore(AiSessionStateStore stateStore, ObjectMapper objectMapper, Clock clock) {
        this.stateStore = stateStore;
        this.objectMapper = objectMapper;
        this.clock = clock;
    }

    public DraftSaveResult saveDraft(Long userId, String sessionId, String scenarioName, JsonNode scene) {
        SessionScope scope = scope(userId, sessionId);
        if (scene == null || !scene.isObject() || !scene.path("devices").isArray()
                || scene.path("devices").isEmpty()) {
            return new DraftSaveResult(false, active(scope) != null);
        }
        Instant now = clock.instant();
        save(scope, new Entry(
                scenarioName == null || scenarioName.isBlank() ? "AI Scenario" : scenarioName,
                scene.deepCopy(),
                now.plus(DRAFT_TTL),
                null,
                null));
        return new DraftSaveResult(true, false);
    }

    public void clearDraft(Long userId, String sessionId) {
        SessionScope scope = scope(userId, sessionId);
        stateStore.remove(scope.userId(), scope.sessionId(), AiSessionStateStore.Kind.SCENARIO_DRAFT);
    }

    public void clearPendingApplication(Long userId, String sessionId) {
        SessionScope scope = scope(userId, sessionId);
        Entry entry = active(scope);
        if (entry != null && entry.pendingPreview() != null) {
            save(scope, entry.withPending(null, null));
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
        save(scope, pending);
        return Optional.of(toPending(pending));
    }

    public Optional<PendingApplication> pendingApplication(Long userId, String sessionId) {
        Entry entry = active(scope(userId, sessionId));
        if (entry == null || entry.pendingPreview() == null || entry.pendingExpiresAt() == null) {
            return Optional.empty();
        }
        if (!entry.pendingExpiresAt().isAfter(clock.instant())) {
            save(scope(userId, sessionId), entry.withPending(null, null));
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
        save(scope, refreshed);
        return Optional.of(toPending(refreshed));
    }

    public void completeApplication(Long userId, String sessionId) {
        clearDraft(userId, sessionId);
    }

    public void clearSession(Long userId, String sessionId) {
        if (userId == null || sessionId == null || sessionId.isBlank()) return;
        stateStore.remove(userId, sessionId, AiSessionStateStore.Kind.SCENARIO_DRAFT);
    }

    public void clearUser(Long userId) {
        if (userId == null) return;
        stateStore.removeUser(userId);
    }

    private Entry active(SessionScope scope) {
        AiSessionStateStore.Snapshot snapshot = stateStore.get(
                scope.userId(), scope.sessionId(), AiSessionStateStore.Kind.SCENARIO_DRAFT,
                clock.instant()).orElse(null);
        if (snapshot == null) return null;
        try {
            JsonNode payload = snapshot.payload();
            String scenarioName = payload.path("scenarioName").asText("AI Scenario");
            JsonNode scene = payload.path("scene");
            if (!scene.isObject()) throw new IllegalArgumentException("missing scene");
            BoardReplacementPreviewDto preview = payload.hasNonNull("pendingPreview")
                    ? previewFromJson(payload.get("pendingPreview"))
                    : null;
            Instant pendingExpiresAt = payload.hasNonNull("pendingExpiresAt")
                    ? Instant.parse(payload.path("pendingExpiresAt").asText())
                    : null;
            return new Entry(scenarioName, scene.deepCopy(), snapshot.expiresAt(), preview, pendingExpiresAt);
        } catch (Exception e) {
            stateStore.remove(scope.userId(), scope.sessionId(), AiSessionStateStore.Kind.SCENARIO_DRAFT,
                    snapshot.version());
            return null;
        }
    }

    private void save(SessionScope scope, Entry entry) {
        ObjectNode payload = JsonNodeFactory.instance.objectNode();
        payload.put("scenarioName", entry.scenarioName());
        payload.set("scene", entry.scene().deepCopy());
        if (entry.pendingPreview() != null) {
            payload.set("pendingPreview", objectMapper.valueToTree(entry.pendingPreview()));
        }
        if (entry.pendingExpiresAt() != null) {
            payload.put("pendingExpiresAt", entry.pendingExpiresAt().toString());
        }
        stateStore.put(scope.userId(), scope.sessionId(), AiSessionStateStore.Kind.SCENARIO_DRAFT,
                payload, entry.draftExpiresAt());
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

    private BoardReplacementPreviewDto previewFromJson(JsonNode source) {
        if (source == null || !source.isObject()) {
            throw new IllegalArgumentException("missing pending preview");
        }
        return BoardReplacementPreviewDto.builder()
                .impactToken(source.path("impactToken").asText(null))
                .deviceCount(source.path("deviceCount").asInt())
                .environmentVariableCount(source.path("environmentVariableCount").asInt())
                .ruleCount(source.path("ruleCount").asInt())
                .specificationCount(source.path("specificationCount").asInt())
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

    public record DraftSaveResult(boolean draftStored, boolean previousDraftRetained) {
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
