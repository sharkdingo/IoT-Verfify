package cn.edu.nju.Iot_Verify.service.impl;

import java.time.Duration;
import java.util.concurrent.atomic.AtomicLong;

/** Tracks how long a local worker has gone without confirming its distributed lease. */
final class LeaseConfirmation {

    private final AtomicLong lastConfirmedNanos = new AtomicLong(System.nanoTime());

    void confirm() {
        lastConfirmedNanos.set(System.nanoTime());
    }

    boolean isUnconfirmedFor(Duration duration) {
        long elapsed = System.nanoTime() - lastConfirmedNanos.get();
        return elapsed >= duration.toNanos();
    }
}
