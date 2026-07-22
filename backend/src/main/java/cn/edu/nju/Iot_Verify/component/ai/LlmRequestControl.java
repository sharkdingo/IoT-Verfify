package cn.edu.nju.Iot_Verify.component.ai;

import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.atomic.AtomicReference;
import java.util.function.BooleanSupplier;

/** Owns the cancellable transport handle for the current provider request. */
public final class LlmRequestControl {

    private final BooleanSupplier stopSignal;
    private final AtomicBoolean cancelled = new AtomicBoolean(false);
    private final AtomicReference<AutoCloseable> activeHandle = new AtomicReference<>();

    public LlmRequestControl() {
        this(() -> false);
    }

    public LlmRequestControl(BooleanSupplier stopSignal) {
        this.stopSignal = Objects.requireNonNull(stopSignal, "stopSignal must not be null");
    }

    public boolean isCancellationRequested() {
        if (cancelled.get()) return true;
        if (stopSignal.getAsBoolean()) {
            cancel();
            return true;
        }
        return false;
    }

    public void attach(AutoCloseable handle) {
        Objects.requireNonNull(handle, "handle must not be null");
        AutoCloseable previous = activeHandle.getAndSet(handle);
        closeQuietly(previous);
        if (isCancellationRequested() && activeHandle.compareAndSet(handle, null)) {
            closeQuietly(handle);
        }
    }

    public void detach(AutoCloseable handle) {
        activeHandle.compareAndSet(handle, null);
    }

    public void cancel() {
        cancelled.set(true);
        closeQuietly(activeHandle.getAndSet(null));
    }

    private void closeQuietly(AutoCloseable handle) {
        if (handle == null) return;
        try {
            handle.close();
        } catch (Exception ignored) {
            // Provider shutdown/cancellation is best-effort and must remain idempotent.
        }
    }
}
