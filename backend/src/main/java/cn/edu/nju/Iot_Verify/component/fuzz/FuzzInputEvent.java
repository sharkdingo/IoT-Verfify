package cn.edu.nju.Iot_Verify.component.fuzz;

import java.util.Objects;

/** One model, initialization, or seed input retained as replay evidence. */
public record FuzzInputEvent(
        int step,
        FuzzInputEventKind kind,
        String targetId,
        String property,
        String value,
        FuzzInputEventSource source) {

    public FuzzInputEvent {
        Objects.requireNonNull(source, "input event source must not be null");
    }
}
