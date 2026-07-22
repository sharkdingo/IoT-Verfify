package cn.edu.nju.Iot_Verify.component.ai;

/** Worker-thread context for the currently active, user-cancellable LLM request. */
public final class LlmRequestControlHolder {

    private static final ThreadLocal<LlmRequestControl> CURRENT = new ThreadLocal<>();

    private LlmRequestControlHolder() {
    }

    public static void set(LlmRequestControl control) {
        CURRENT.set(control);
    }

    public static LlmRequestControl currentOrNew() {
        LlmRequestControl control = CURRENT.get();
        return control == null ? new LlmRequestControl() : control;
    }

    public static void clear() {
        CURRENT.remove();
    }
}
