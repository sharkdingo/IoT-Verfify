package cn.edu.nju.Iot_Verify.service.impl;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.ArgumentCaptor;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.data.redis.RedisConnectionFailureException;
import org.springframework.data.redis.core.StringRedisTemplate;
import org.springframework.data.redis.core.ValueOperations;

import java.lang.reflect.Field;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class RedisTokenBlacklistServiceTest {

    @Mock
    private StringRedisTemplate redisTemplate;

    @Mock
    private ValueOperations<String, String> valueOperations;

    private RedisTokenBlacklistService service;

    @BeforeEach
    void setUp() {
        service = new RedisTokenBlacklistService(redisTemplate);
    }

    // --- blacklist ---

    @Test
    void blacklist_setsKeyWithTtl() {
        when(redisTemplate.opsForValue()).thenReturn(valueOperations);

        service.blacklist("test-token", 3600);

        verify(valueOperations).set(
                argThat(key -> key.startsWith("jwt:blacklist:") && !key.contains("test-token")),
                eq("1"),
                eq(3600L),
                eq(TimeUnit.SECONDS)
        );
    }

    @Test
    void blacklist_redisDown_doesNotThrow() {
        when(redisTemplate.opsForValue()).thenThrow(new RedisConnectionFailureException("Connection refused"));

        assertDoesNotThrow(() -> service.blacklist("test-token", 3600));
    }

    // --- isBlacklisted ---

    @Test
    void isBlacklisted_keyExists_returnsTrue() {
        when(redisTemplate.hasKey(anyString())).thenReturn(true);

        assertTrue(service.isBlacklisted("test-token"));
    }

    @Test
    void isBlacklisted_keyMissing_returnsFalse() {
        when(redisTemplate.hasKey(anyString())).thenReturn(false);

        assertFalse(service.isBlacklisted("test-token"));
    }

    @Test
    void isBlacklisted_redisDown_returnsFalse() {
        when(redisTemplate.hasKey(anyString())).thenThrow(new RedisConnectionFailureException("Connection refused"));

        assertFalse(service.isBlacklisted("test-token"));
    }

    // --- SHA-256 key 一致性 ---

    @Test
    void sameToken_producesSameKey() {
        ArgumentCaptor<String> captor = ArgumentCaptor.forClass(String.class);
        when(redisTemplate.hasKey(anyString())).thenReturn(false);

        service.isBlacklisted("token-a");
        service.isBlacklisted("token-a");

        verify(redisTemplate, times(2)).hasKey(captor.capture());
        assertEquals(captor.getAllValues().get(0), captor.getAllValues().get(1));
    }

    @Test
    void differentTokens_produceDifferentKeys() {
        ArgumentCaptor<String> captor = ArgumentCaptor.forClass(String.class);
        when(redisTemplate.hasKey(anyString())).thenReturn(false);

        service.isBlacklisted("token-a");
        service.isBlacklisted("token-b");

        verify(redisTemplate, times(2)).hasKey(captor.capture());
        assertNotEquals(captor.getAllValues().get(0), captor.getAllValues().get(1));
    }

    // --- 日志限流 ---

    @Test
    void logThrottling_sameWindow_logsOnlyOnce() throws Exception {
        when(redisTemplate.hasKey(anyString())).thenThrow(new RedisConnectionFailureException("down"));

        // 将 lastCheckErrorTime 设为"刚刚"，模拟同一个 60 秒窗口内
        Field field = RedisTokenBlacklistService.class.getDeclaredField("lastCheckErrorTime");
        field.setAccessible(true);
        AtomicLong lastCheckErrorTime = (AtomicLong) field.get(service);

        // 第一次调用：限流时间戳为 0，会打日志并更新时间戳
        service.isBlacklisted("token-1");
        long afterFirst = lastCheckErrorTime.get();
        assertTrue(afterFirst > 0, "限流时间戳应已更新");

        // 后续调用在同一窗口内，时间戳不应再变
        service.isBlacklisted("token-2");
        service.isBlacklisted("token-3");
        assertEquals(afterFirst, lastCheckErrorTime.get(), "同一窗口内时间戳不应再更新");
    }

    @Test
    void logThrottling_blacklistAndCheck_independent() throws Exception {
        when(redisTemplate.hasKey(anyString())).thenThrow(new RedisConnectionFailureException("down"));
        when(redisTemplate.opsForValue()).thenThrow(new RedisConnectionFailureException("down"));

        Field blacklistField = RedisTokenBlacklistService.class.getDeclaredField("lastBlacklistErrorTime");
        blacklistField.setAccessible(true);
        Field checkField = RedisTokenBlacklistService.class.getDeclaredField("lastCheckErrorTime");
        checkField.setAccessible(true);

        service.blacklist("token", 100);
        service.isBlacklisted("token");

        AtomicLong blacklistTime = (AtomicLong) blacklistField.get(service);
        AtomicLong checkTime = (AtomicLong) checkField.get(service);

        // 两个限流计数器是不同对象
        assertNotSame(blacklistTime, checkTime, "blacklist 和 check 应使用不同的 AtomicLong 实例");
        // 两个限流时间戳都应已更新
        assertTrue(blacklistTime.get() > 0, "blacklist 限流时间戳应已更新");
        assertTrue(checkTime.get() > 0, "check 限流时间戳应已更新");
    }
}
