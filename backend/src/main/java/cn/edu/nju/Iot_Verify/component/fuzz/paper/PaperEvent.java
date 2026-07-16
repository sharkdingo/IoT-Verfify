package cn.edu.nju.Iot_Verify.component.fuzz.paper;

import cn.edu.nju.Iot_Verify.component.fuzz.FuzzInputEventKind;
import cn.edu.nju.Iot_Verify.component.fuzz.FuzzInputEventSource;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzInputEventDto;

import java.util.Objects;

/**
 * One immutable event in the paper-compatible seed representation.
 *
 * <p>A device value is a legal device mode. An environment value is normally a change
 * rate; direct environment values belong to separately materialized initial state. A
 * rate-free discrete environment may use direct values as a compatibility extension.</p>
 */
public record PaperEvent(Type type, String name, String value, int position) {

    public enum Type {
        DEVICE,
        ENVIRONMENT
    }

    public PaperEvent {
        type = Objects.requireNonNull(type, "type must not be null");
        name = requireText(name, "name");
        value = requireText(value, "value");
        if (position < 1) {
            throw new IllegalArgumentException("position must be at least 1");
        }
        if (type == Type.DEVICE && position != 1) {
            throw new IllegalArgumentException("device events are only legal at position 1");
        }
    }

    /** Alias for callers that use target terminology instead of name. */
    public String target() {
        return name;
    }

    /**
     * Lossless adapter to the persisted fuzz-input event contract.
     * Environment event values are validated against the domain's change-rate values.
     */
    public FuzzInputEventDto toFuzzInputEventDto(PaperEventDomain eventDomain) {
        PaperEventDomainSnapshot snapshot = PaperEventDomainSnapshot.copyOf(eventDomain);
        if (position > snapshot.traceLength()) {
            throw new IllegalArgumentException("event position exceeds the domain trace length");
        }
        if (type == Type.DEVICE) {
            PaperDeviceDomain device = snapshot.device(name);
            if (device == null || !device.legalValues().contains(value)) {
                throw new IllegalArgumentException("device event is outside its legal domain");
            }
            return FuzzInputEventDto.builder()
                    .step(position - 1)
                    .kind(FuzzInputEventKind.DEVICE_STATE.name())
                    .targetId(device.targetId())
                    .property(device.property())
                    .value(value)
                    .source(FuzzInputEventSource.SEED_EVENT.name())
                    .build();
        }
        PaperEnvironmentDomain environment = snapshot.environment(name);
        if (environment == null || !environment.isValidEventValue(value)) {
            throw new IllegalArgumentException("environment event is outside its legal domain");
        }
        return FuzzInputEventDto.builder()
                .step(position - 1)
                .kind((!environment.hasRateDomain()
                        ? FuzzInputEventKind.ENVIRONMENT_VALUE
                        : FuzzInputEventKind.ENVIRONMENT_RATE).name())
                .targetId(environment.targetId())
                .property(environment.property())
                .value(value)
                .source(FuzzInputEventSource.SEED_EVENT.name())
                .build();
    }

    private static String requireText(String value, String field) {
        if (value == null || value.isBlank()) {
            throw new IllegalArgumentException(field + " must not be blank");
        }
        return value.trim();
    }
}
