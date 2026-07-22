package cn.edu.nju.Iot_Verify.service;

import org.junit.jupiter.api.Test;

import java.time.Duration;
import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.when;

class FormalOperationAdmissionTest {

    @Test
    void executeOwnsAndChecksFormalLeaseAroundOperation() {
        UserOperationGuard guard = mock(UserOperationGuard.class);
        UserOperationGuard.Lease lease = mock(UserOperationGuard.Lease.class);
        when(guard.renewableLeaseTtl()).thenReturn(Duration.ofMinutes(2));
        when(guard.acquire(7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(2)))
                .thenReturn(lease);
        AtomicBoolean invoked = new AtomicBoolean();

        String result = new FormalOperationAdmission(guard).execute(7L, () -> {
            invoked.set(true);
            return "done";
        });

        assertEquals("done", result);
        assertTrue(invoked.get());
        verify(lease, times(2)).requireActive();
        verify(lease).close();
        verify(guard).acquire(7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(2));
    }
}
