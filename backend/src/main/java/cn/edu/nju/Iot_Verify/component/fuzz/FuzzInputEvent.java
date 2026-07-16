package cn.edu.nju.Iot_Verify.component.fuzz;

/** One model, initialization, or seed input retained as replay evidence. */
public record FuzzInputEvent(
        int step,
        FuzzInputEventKind kind,
        String targetId,
        String property,
        String value,
        FuzzInputEventSource source) {

    public FuzzInputEvent {
        source = source == null ? FuzzInputEventSource.MODEL_CHOICE : source;
    }

    /** Backward-compatible constructor for ordinary nondeterministic model choices. */
    public FuzzInputEvent(
            int step,
            FuzzInputEventKind kind,
            String targetId,
            String property,
            String value) {
        this(step, kind, targetId, property, value, FuzzInputEventSource.MODEL_CHOICE);
    }
}
