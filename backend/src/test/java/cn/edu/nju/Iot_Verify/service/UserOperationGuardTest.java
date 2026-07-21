package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.exception.UserOperationBusyException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.data.redis.RedisConnectionFailureException;
import org.springframework.data.redis.core.StringRedisTemplate;
import org.springframework.data.redis.core.ValueOperations;
import org.springframework.data.redis.core.script.RedisScript;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.verify;
import static org.mockito.ArgumentMatchers.anyList;

@ExtendWith(MockitoExtension.class)
class UserOperationGuardTest {

    @Mock
    private StringRedisTemplate redisTemplate;

    @Mock
    private ValueOperations<String, String> valueOperations;

    @Test
    void redisSlotPreventsSameUserAdmissionAcrossGuardInstances() {
        when(redisTemplate.opsForValue()).thenReturn(valueOperations);
        when(valueOperations.setIfAbsent(anyString(), anyString(), any(Duration.class)))
                .thenReturn(true, false);
        UserOperationGuard firstInstance = new UserOperationGuard(redisTemplate);
        UserOperationGuard secondInstance = new UserOperationGuard(redisTemplate);

        UserOperationGuard.Lease lease = firstInstance.acquire(
                7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(1));
        assertThrows(UserOperationBusyException.class, () -> secondInstance.acquire(
                7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(1)));

        lease.close();
    }

    @Test
    void redisFailureFallsBackToReleasableProcessLocalSlot() {
        when(redisTemplate.opsForValue()).thenThrow(new RedisConnectionFailureException("down"));
        UserOperationGuard guard = new UserOperationGuard(redisTemplate);

        UserOperationGuard.Lease lease = guard.acquire(
                7L, UserOperationGuard.Kind.CHAT, 1, Duration.ofMinutes(1));
        assertThrows(UserOperationBusyException.class, () -> guard.acquire(
                7L, UserOperationGuard.Kind.CHAT, 1, Duration.ofMinutes(1)));
        lease.close();

        UserOperationGuard.Lease next = assertDoesNotThrow(() -> guard.acquire(
                7L, UserOperationGuard.Kind.CHAT, 1, Duration.ofMinutes(1)));
        next.close();
    }

    @Test
    void activeRedisLeaseIsRenewedAndClosedLeaseStopsRenewing() {
        when(redisTemplate.opsForValue()).thenReturn(valueOperations);
        when(valueOperations.setIfAbsent(anyString(), anyString(), any(Duration.class))).thenReturn(true);
        when(redisTemplate.execute(
                any(RedisScript.class), anyList(), any(), any())).thenReturn(1L);
        UserOperationGuard guard = new UserOperationGuard(redisTemplate);

        UserOperationGuard.Lease lease = guard.acquire(
                7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(1));
        guard.renewActiveLeases();

        verify(redisTemplate).execute(any(RedisScript.class), anyList(), any(), any());
        lease.close();
        guard.renewActiveLeases();
        verify(redisTemplate, times(1)).execute(any(RedisScript.class), anyList(), any(), any());
    }

    @Test
    void leaseOwnershipMismatchStopsTheOldOperation() {
        when(redisTemplate.opsForValue()).thenReturn(valueOperations);
        when(valueOperations.setIfAbsent(anyString(), anyString(), any(Duration.class))).thenReturn(true);
        when(redisTemplate.execute(any(RedisScript.class), anyList(), any(), any())).thenReturn(0L);
        UserOperationGuard guard = new UserOperationGuard(redisTemplate);
        UserOperationGuard.Lease lease = guard.acquire(
                7L, UserOperationGuard.Kind.FORMAL, 1, Duration.ofMinutes(1));

        guard.renewActiveLeases();

        assertFalse(lease.isActive());
        assertThrows(ServiceUnavailableException.class, lease::requireActive);
        lease.close();
    }
}
