package cn.edu.nju.Iot_Verify.component.ai.state;

import com.fasterxml.jackson.databind.JsonNode;

import java.time.Instant;
import java.util.Optional;

/** Shared persistence boundary for short-lived, session-scoped AI workflow state. */
public interface AiSessionStateStore {

    enum Kind {
        TASK_CONTINUATION,
        SCENARIO_DRAFT,
        DESTRUCTIVE_ACTION
    }

    record Snapshot(JsonNode payload, Instant expiresAt, long version) {
    }

    Optional<Snapshot> get(Long userId, String sessionId, Kind kind, Instant now);

    void put(Long userId, String sessionId, Kind kind, JsonNode payload, Instant expiresAt);

    boolean remove(Long userId, String sessionId, Kind kind, long expectedVersion);

    void remove(Long userId, String sessionId, Kind kind);

    void removeSession(Long userId, String sessionId);

    void removeUser(Long userId);
}
