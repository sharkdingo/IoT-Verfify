package cn.edu.nju.Iot_Verify.component.fuzz.paper;

import java.util.Comparator;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;

/** Immutable random initialization identity, initial overrides, and ordinary events. */
public record PaperSeed(
        long initializationNonce,
        List<PaperInitialValue> initialOverrides,
        List<PaperEvent> events) {

    public static final int MAX_EVENTS = 10_000;
    public static final int MAX_INITIAL_OVERRIDES = PaperEventDomain.MAX_TARGETS_PER_TYPE * 3;

    public PaperSeed {
        if (initialOverrides == null) {
            throw new IllegalArgumentException("initialOverrides must not be null");
        }
        if (events == null) {
            throw new IllegalArgumentException("events must not be null");
        }
        if (initialOverrides.size() > MAX_INITIAL_OVERRIDES) {
            throw new IllegalArgumentException(
                    "seed contains more than " + MAX_INITIAL_OVERRIDES + " initial overrides");
        }
        if (events.size() > MAX_EVENTS) {
            throw new IllegalArgumentException("seed contains more than " + MAX_EVENTS + " events");
        }
        List<PaperInitialValue> orderedOverrides = initialOverrides.stream()
                .map(value -> Objects.requireNonNull(value, "initial override must not be null"))
                .sorted(Comparator.comparing(PaperInitialValue::type)
                        .thenComparing(PaperInitialValue::targetId)
                        .thenComparing(PaperInitialValue::property))
                .toList();
        Set<PaperInitialValue.Target> overriddenTargets = new HashSet<>();
        for (PaperInitialValue override : orderedOverrides) {
            if (!overriddenTargets.add(override.target())) {
                throw new IllegalArgumentException(
                        "a seed cannot override the same initial target twice");
            }
        }
        List<PaperEvent> ordered = events.stream()
                .map(event -> Objects.requireNonNull(event, "seed event must not be null"))
                .sorted(Comparator.comparingInt(PaperEvent::position)
                        .thenComparing(PaperEvent::type)
                        .thenComparing(PaperEvent::name))
                .toList();
        Set<EventSlot> slots = new HashSet<>();
        for (PaperEvent event : ordered) {
            if (!slots.add(new EventSlot(event.type(), event.name(), event.position()))) {
                throw new IllegalArgumentException(
                        "a seed cannot assign the same event target twice at one position");
            }
        }
        initialOverrides = List.copyOf(orderedOverrides);
        events = List.copyOf(ordered);
    }

    public PaperSeed(long initializationNonce, List<PaperEvent> events) {
        this(initializationNonce, List.of(), events);
    }

    public static PaperSeed empty(long initializationNonce) {
        return new PaperSeed(initializationNonce, List.of(), List.of());
    }

    public static PaperSeed empty() {
        return empty(0L);
    }

    private record EventSlot(PaperEvent.Type type, String name, int position) {
    }
}
