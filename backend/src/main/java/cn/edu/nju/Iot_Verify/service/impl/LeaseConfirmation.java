package cn.edu.nju.Iot_Verify.service.impl;

import java.time.Duration;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.LongSupplier;

/** Tracks how long a local worker has gone without confirming its distributed lease. */
final class LeaseConfirmation {

    private final AtomicLong lastConfirmedNanos;

    LeaseConfirmation() {
        this(System.nanoTime());
    }

    LeaseConfirmation(long initialConfirmedNanos) {
        lastConfirmedNanos = new AtomicLong(initialConfirmedNanos);
    }

    void confirmAt(long confirmationStartedNanos) {
        if (confirmationStartedNanos == Long.MIN_VALUE) return;
        lastConfirmedNanos.updateAndGet(previous -> Math.max(previous, confirmationStartedNanos));
    }

    boolean isUnconfirmedFor(Duration duration) {
        return isUnconfirmedFor(duration, System::nanoTime);
    }

    boolean isUnconfirmedFor(Duration duration, LongSupplier monotonicClock) {
        if (duration == null || duration.isNegative() || duration.isZero()
                || monotonicClock == null) {
            return true;
        }
        long elapsed = monotonicClock.getAsLong() - lastConfirmedNanos.get();
        return elapsed >= duration.toNanos();
    }
}
