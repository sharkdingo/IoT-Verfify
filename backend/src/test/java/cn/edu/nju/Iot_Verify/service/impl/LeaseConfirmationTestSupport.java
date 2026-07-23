package cn.edu.nju.Iot_Verify.service.impl;

import java.lang.reflect.Field;
import java.time.Duration;
import java.util.Map;
import java.util.concurrent.atomic.AtomicLong;

final class LeaseConfirmationTestSupport {

    private LeaseConfirmationTestSupport() {
    }

    static void ageExecutionLease(
            Object service, String executionMapField, Object executionKey, Duration elapsed) throws Exception {
        Field mapField = service.getClass().getDeclaredField(executionMapField);
        mapField.setAccessible(true);
        Object execution = ((Map<?, ?>) mapField.get(service)).get(executionKey);
        if (execution == null) {
            throw new AssertionError("No local execution registered for " + executionKey);
        }
        Field confirmationField = execution.getClass().getDeclaredField("leaseConfirmation");
        confirmationField.setAccessible(true);
        LeaseConfirmation confirmation = (LeaseConfirmation) confirmationField.get(execution);
        Field lastConfirmedField = LeaseConfirmation.class.getDeclaredField("lastConfirmedNanos");
        lastConfirmedField.setAccessible(true);
        ((AtomicLong) lastConfirmedField.get(confirmation))
                .set(System.nanoTime() - elapsed.toNanos());
    }
}
