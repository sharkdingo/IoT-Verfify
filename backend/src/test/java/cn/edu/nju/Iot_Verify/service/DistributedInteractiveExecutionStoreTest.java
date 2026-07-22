package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.model.InteractiveOperationStage;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.data.redis.core.StringRedisTemplate;
import org.springframework.data.redis.core.ValueOperations;
import org.springframework.data.redis.core.script.RedisScript;

import java.time.Duration;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.any;
import static org.mockito.ArgumentMatchers.anyList;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.verify;
import static org.mockito.Mockito.times;
import static org.mockito.Mockito.when;
import static org.mockito.Mockito.lenient;

@ExtendWith(MockitoExtension.class)
class DistributedInteractiveExecutionStoreTest {

    @Mock private StringRedisTemplate redisTemplate;
    @Mock private ValueOperations<String, String> values;

    private DistributedInteractiveExecutionStore store;

    @BeforeEach
    void setUp() {
        lenient().when(redisTemplate.opsForValue()).thenReturn(values);
        store = new DistributedInteractiveExecutionStore(redisTemplate);
    }

    @Test
    void remoteInstanceCanReadStatusAndPublishCancellation() {
        when(redisTemplate.execute(any(RedisScript.class), anyList()))
                .thenReturn("RUNNING\nREQUESTING_MODEL\n" + (System.currentTimeMillis() - 20));
        when(redisTemplate.execute(any(RedisScript.class), anyList(), any(), any())).thenReturn(1L);

        var status = store.getStatus("recommendation", 7L, "request-123").orElseThrow();
        boolean cancelled = store.requestCancellation("recommendation", 7L, "request-123");

        assertEquals("RUNNING", status.getState());
        assertEquals(InteractiveOperationStage.REQUESTING_MODEL, status.getStage());
        assertTrue(cancelled);
        verify(redisTemplate).execute(
                any(RedisScript.class),
                eq(java.util.List.of(
                        "iot-verify:interactive:recommendation:7:request-123:owner",
                        "iot-verify:interactive:recommendation:7:request-123:cancel",
                        "iot-verify:interactive:recommendation:7:request-123:status")),
                eq("30000"), eq("CANCELLING"));
    }

    @Test
    void duplicateRequestOwnershipIsRejectedAcrossInstances() {
        when(values.setIfAbsent(anyString(), anyString(), any(Duration.class))).thenReturn(false);

        DistributedInteractiveExecutionStore.BusyException error = assertThrows(
                DistributedInteractiveExecutionStore.BusyException.class,
                () -> store.acquire("fix", 7L, "request-123", false));

        assertEquals(DistributedInteractiveExecutionStore.BusyScope.REQUEST, error.getScope());
    }

    @Test
    void staleActiveStatusIsIgnoredAfterItsOwnerLeaseDisappears() {
        when(redisTemplate.execute(any(RedisScript.class), anyList())).thenReturn(null);

        assertTrue(store.getStatus("fix", 7L, "request-123").isEmpty());
    }

    @Test
    void partialRedisFailureFallsBackToLocalOwnershipWithoutSelfCancellation() {
        when(values.setIfAbsent(anyString(), anyString(), any(Duration.class))).thenReturn(true);

        var lease = store.acquire("fix", 7L, "request-123", false);

        assertFalse(store.shouldStop(lease));
    }

    @Test
    void activeLeasePollUsesTokenFencedRenewalAndContinuesWithoutCancellation() {
        when(values.setIfAbsent(anyString(), anyString(), any(Duration.class))).thenReturn(true);
        when(redisTemplate.execute(any(RedisScript.class), anyList(),
                any(), any(), any(), any(), any())).thenReturn(1L);
        when(redisTemplate.execute(any(RedisScript.class), anyList(),
                any(), any(), any())).thenReturn(0L);

        var lease = store.acquire("fix", 7L, "request-123", false);

        assertFalse(store.shouldStop(lease));
        verify(redisTemplate).execute(any(RedisScript.class),
                eq(java.util.List.of(
                        "iot-verify:interactive:fix:7:request-123:owner",
                        "iot-verify:interactive:fix:7:active",
                        "iot-verify:interactive:fix:7:request-123:status",
                        "iot-verify:interactive:fix:7:request-123:cancel")),
                any(), eq("30000"), eq("0"));
    }

    @Test
    void cancellationObservationStillRenewsOwnershipUntilTheCallableExits() {
        when(values.setIfAbsent(anyString(), anyString(), any(Duration.class))).thenReturn(true);
        when(redisTemplate.execute(any(RedisScript.class), anyList(),
                any(), any(), any(), any(), any())).thenReturn(1L);
        when(redisTemplate.execute(any(RedisScript.class), anyList(),
                any(), any(), any())).thenReturn(1L);
        var lease = store.acquire("fix", 7L, "request-123", false);

        assertTrue(store.shouldStop(lease));
        assertTrue(store.shouldStop(lease));

        verify(redisTemplate, times(2)).execute(any(RedisScript.class),
                eq(java.util.List.of(
                        "iot-verify:interactive:fix:7:request-123:owner",
                        "iot-verify:interactive:fix:7:active",
                        "iot-verify:interactive:fix:7:request-123:status",
                        "iot-verify:interactive:fix:7:request-123:cancel")),
                any(), eq("30000"), eq("0"));
    }
}
