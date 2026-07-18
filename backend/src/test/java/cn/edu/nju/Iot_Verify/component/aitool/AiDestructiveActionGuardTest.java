package cn.edu.nju.Iot_Verify.component.aitool;

import cn.edu.nju.Iot_Verify.component.ai.state.InMemoryAiSessionStateStore;
import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.time.Clock;
import java.time.Instant;
import java.time.ZoneOffset;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class AiDestructiveActionGuardTest {

    private AiDestructiveActionGuard guard;

    @BeforeEach
    void setUp() {
        guard = new AiDestructiveActionGuard(new ObjectMapper());
        UserContextHolder.setUserId(1L);
        UserContextHolder.setChatSessionId("session-1");
    }

    @AfterEach
    void tearDown() {
        UserContextHolder.clear();
    }

    @Test
    void consume_shouldBindExactActionAndAllowOnlyOneUse() {
        Map<String, Object> preview = Map.of("rule", Map.of("id", 7, "label", "Alarm"));
        String token = guard.issue(1L, "manage_rule", "7", preview, "domain-token");
        UserContextHolder.setDestructiveActionConfirmed(true);

        AiDestructiveActionGuard.ConsumeResult first =
                guard.consume(1L, "manage_rule", "7", token, preview);
        AiDestructiveActionGuard.ConsumeResult replay =
                guard.consume(1L, "manage_rule", "7", token, preview);

        assertTrue(first.approved());
        assertEquals("domain-token", first.domainImpactToken());
        assertFalse(replay.approved());
        assertEquals("CONFIRMATION_MISSING", replay.errorCode());
    }

    @Test
    void consume_shouldRejectAnotherUserSessionToolOrTargetWithoutConsumingMatch() {
        Map<String, Object> preview = Map.of("traceId", 11, "stateCount", 3);
        String token = guard.issue(1L, "delete_trace", "11", preview, null);
        UserContextHolder.setDestructiveActionConfirmed(true);

        assertEquals("CONFIRMATION_MISSING",
                guard.consume(2L, "delete_trace", "11", token, preview).errorCode());

        UserContextHolder.setChatSessionId("session-2");
        assertEquals("CONFIRMATION_MISSING",
                guard.consume(1L, "delete_trace", "11", token, preview).errorCode());

        UserContextHolder.setChatSessionId("session-1");
        assertEquals("CONFIRMATION_MISMATCH",
                guard.consume(1L, "delete_simulation_trace", "11", token, preview).errorCode());
        assertEquals("CONFIRMATION_MISMATCH",
                guard.consume(1L, "delete_trace", "12", token, preview).errorCode());
        assertEquals("CONFIRMATION_MISMATCH",
                guard.consume(1L, "delete_trace", "11", "wrong-token", preview).errorCode());

        assertTrue(guard.consume(1L, "delete_trace", "11", token, preview).approved());
    }

    @Test
    void consume_shouldRejectPreviewDriftAndInvalidateOldToken() {
        Map<String, Object> original = new LinkedHashMap<>();
        original.put("specification", Map.of("id", "spec-1", "conditions", List.of("smoke")));
        String token = guard.issue(1L, "manage_spec", "spec-1", original, null);
        UserContextHolder.setDestructiveActionConfirmed(true);

        Map<String, Object> changed = Map.of(
                "specification", Map.of("id", "spec-1", "conditions", List.of("smoke", "heat")));
        AiDestructiveActionGuard.ConsumeResult stale =
                guard.consume(1L, "manage_spec", "spec-1", token, changed);
        AiDestructiveActionGuard.ConsumeResult replay =
                guard.consume(1L, "manage_spec", "spec-1", token, original);

        assertFalse(stale.approved());
        assertEquals("CONFIRMATION_STALE", stale.errorCode());
        assertEquals("CONFIRMATION_MISSING", replay.errorCode());
    }

    @Test
    void issue_shouldReplaceEarlierPendingActionInSameSession() {
        String first = guard.issue(1L, "manage_rule", "1", Map.of("id", 1), null);
        String second = guard.issue(1L, "manage_rule", "2", Map.of("id", 2), null);
        UserContextHolder.setDestructiveActionConfirmed(true);

        assertNotEquals(first, second);
        assertEquals("CONFIRMATION_MISMATCH",
                guard.consume(1L, "manage_rule", "1", first, Map.of("id", 1)).errorCode());
        assertTrue(guard.consume(1L, "manage_rule", "2", second, Map.of("id", 2)).approved());
    }

    @Test
    void consume_shouldRequireAnExplicitConfirmationTurn() {
        Map<String, Object> preview = Map.of("simulationId", 5);
        String token = guard.issue(1L, "delete_simulation_trace", "5", preview, null);

        AiDestructiveActionGuard.ConsumeResult result =
                guard.consume(1L, "delete_simulation_trace", "5", token, preview);

        assertFalse(result.approved());
        assertEquals("CONFIRMATION_REQUIRED", result.errorCode());
    }

    @Test
    void consume_shouldNotTreatSceneReplacementConfirmationAsDeletionAuthorization() {
        Map<String, Object> preview = Map.of("rule", Map.of("id", 7, "label", "Alarm"));
        String token = guard.issue(1L, "manage_rule", "7", preview, "domain-token");
        UserContextHolder.setSceneReplacementConfirmed(true);

        AiDestructiveActionGuard.ConsumeResult result =
                guard.consume(1L, "manage_rule", "7", token, preview);

        assertFalse(result.approved());
        assertEquals("CONFIRMATION_REQUIRED", result.errorCode());
        UserContextHolder.setDestructiveActionConfirmed(true);
        assertTrue(guard.consume(1L, "manage_rule", "7", token, preview).approved());
    }

    @Test
    void consume_shouldKeepDefaultTemplateResetConfirmationScopedToResetTool() {
        Map<String, Object> preview = Map.of("rule", Map.of("id", 7, "label", "Alarm"));
        String token = guard.issue(1L, "manage_rule", "7", preview, "domain-token");
        UserContextHolder.setDefaultTemplateResetConfirmed(true);

        AiDestructiveActionGuard.ConsumeResult result =
                guard.consume(1L, "manage_rule", "7", token, preview);

        assertFalse(result.approved());
        assertEquals("CONFIRMATION_REQUIRED", result.errorCode());
    }

    @Test
    void pendingContext_shouldExposeCompactServerSideConfirmationData() {
        String token = guard.issue(
                1L, "delete_device", "alarm_1", Map.of("id", "alarm_1"), "domain-token");

        AiDestructiveActionGuard.PendingActionContext context = guard
                .pendingContext(1L, "session-1")
                .orElseThrow();

        assertEquals("delete_device", context.toolName());
        assertEquals("alarm_1", context.targetKey());
        assertEquals(token, context.impactToken());
    }

    @Test
    void anotherGuardInstanceCanConsumeThePersistedSingleUseConfirmation() {
        InMemoryAiSessionStateStore sharedState = new InMemoryAiSessionStateStore();
        Clock clock = Clock.fixed(Instant.parse("2026-07-17T00:00:00Z"), ZoneOffset.UTC);
        AiDestructiveActionGuard issuer = new AiDestructiveActionGuard(
                new ObjectMapper(), sharedState, clock);
        AiDestructiveActionGuard consumer = new AiDestructiveActionGuard(
                new ObjectMapper(), sharedState, clock);
        Map<String, Object> preview = Map.of("id", 17);
        String token = issuer.issue(1L, "delete_trace", "17", preview, null);
        UserContextHolder.setDestructiveActionConfirmed(true);

        assertTrue(consumer.consume(1L, "delete_trace", "17", token, preview).approved());
        assertEquals("CONFIRMATION_MISSING",
                issuer.consume(1L, "delete_trace", "17", token, preview).errorCode());
    }
}
