package cn.edu.nju.Iot_Verify.component.ai;

import cn.edu.nju.Iot_Verify.component.ai.state.InMemoryAiSessionStateStore;
import org.junit.jupiter.api.Test;

import java.time.Clock;
import java.time.Duration;
import java.time.Instant;
import java.time.ZoneId;
import java.time.ZoneOffset;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class AiTaskContinuationStoreTest {

    @Test
    void keepsOriginalObjectiveWithinTheSameUserAndSession() {
        MutableClock clock = new MutableClock(Instant.parse("2026-07-17T00:00:00Z"));
        AiTaskContinuationStore store = new AiTaskContinuationStore(clock);

        store.save(1L, "s1", "  delete the old sensor, create a replacement, then verify  ");

        assertEquals(
                "delete the old sensor, create a replacement, then verify",
                store.pendingObjective(1L, "s1").orElseThrow());
        assertTrue(store.pendingObjective(1L, "s2").isEmpty());
        assertTrue(store.pendingObjective(2L, "s1").isEmpty());
    }

    @Test
    void expiresContinuationAtTheConfirmationBoundaryTtl() {
        MutableClock clock = new MutableClock(Instant.parse("2026-07-17T00:00:00Z"));
        AiTaskContinuationStore store = new AiTaskContinuationStore(clock);
        store.save(1L, "s1", "replace and verify");

        clock.advance(AiTaskContinuationStore.CONTINUATION_TTL.plus(Duration.ofSeconds(1)));

        assertTrue(store.pendingObjective(1L, "s1").isEmpty());
    }

    @Test
    void preservesPendingChoiceAndRecentUserUpdatesWithoutReplacingTheOriginalGoal() {
        MutableClock clock = new MutableClock(Instant.parse("2026-07-17T00:00:00Z"));
        AiTaskContinuationStore store = new AiTaskContinuationStore(clock);
        store.savePendingStep(
                1L,
                "s1",
                "delete the old sensor, create a replacement, then verify",
                "delete the old sensor, create a replacement, then verify",
                "delete_device",
                "{\"suggestedLabel\":\"Hall Sensor 2\"}");

        store.rememberUserMessage(1L, "s1", "Keep the existing rules");
        AiTaskContinuationStore.ContinuationContext context = store
                .pendingContext(1L, "s1")
                .orElseThrow();

        assertEquals("delete the old sensor, create a replacement, then verify",
                context.originalObjective());
        assertEquals("delete_device", context.pendingToolName());
        assertEquals("{\"suggestedLabel\":\"Hall Sensor 2\"}", context.pendingResult());
        assertEquals(java.util.List.of("Keep the existing rules"), context.recentUserMessages());
    }

    @Test
    void anotherStoreInstanceCanResumeThePersistedTask() {
        Clock clock = Clock.fixed(Instant.parse("2026-07-17T00:00:00Z"), ZoneOffset.UTC);
        InMemoryAiSessionStateStore sharedState = new InMemoryAiSessionStateStore();
        AiTaskContinuationStore writer = new AiTaskContinuationStore(sharedState, clock);
        AiTaskContinuationStore reader = new AiTaskContinuationStore(sharedState, clock);

        writer.save(1L, "s1", "replace the sensor and verify");

        assertEquals("replace the sensor and verify",
                reader.pendingObjective(1L, "s1").orElseThrow());
    }

    private static final class MutableClock extends Clock {
        private Instant instant;

        private MutableClock(Instant instant) {
            this.instant = instant;
        }

        private void advance(Duration duration) {
            instant = instant.plus(duration);
        }

        @Override
        public ZoneId getZone() {
            return ZoneOffset.UTC;
        }

        @Override
        public Clock withZone(ZoneId zone) {
            return this;
        }

        @Override
        public Instant instant() {
            return instant;
        }
    }
}
