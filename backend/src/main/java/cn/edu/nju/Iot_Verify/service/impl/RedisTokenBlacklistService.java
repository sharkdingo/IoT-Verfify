package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.service.TokenBlacklistService;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.data.redis.core.StringRedisTemplate;
import org.springframework.lang.NonNull;
import org.springframework.stereotype.Service;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.util.HexFormat;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicLong;

@Slf4j
@Service
@RequiredArgsConstructor
public class RedisTokenBlacklistService implements TokenBlacklistService {

    private static final String BLACKLIST_PREFIX = "jwt:blacklist:";
    private static final long LOG_INTERVAL_MS = 60_000;

    private final StringRedisTemplate redisTemplate;
    private final AtomicLong lastBlacklistErrorTime = new AtomicLong(0);
    private final AtomicLong lastCheckErrorTime = new AtomicLong(0);

    @Override
    public void blacklist(String token, long expirationSeconds) {
        try {
            String key = toSha256Key(token);
            redisTemplate.opsForValue().set(key, "1", expirationSeconds, TimeUnit.SECONDS);
        } catch (Exception e) {
            logThrottled(lastBlacklistErrorTime, "Redis unavailable, failed to blacklist token", e);
        }
    }

    @Override
    public boolean isBlacklisted(String token) {
        try {
            String key = toSha256Key(token);
            return Boolean.TRUE.equals(redisTemplate.hasKey(key));
        } catch (Exception e) {
            logThrottled(lastCheckErrorTime, "Redis unavailable, blacklist check skipped", e);
            return false;
        }
    }

    @NonNull
    private String toSha256Key(String token) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] hashBytes = digest.digest(token.getBytes(StandardCharsets.UTF_8));
            return BLACKLIST_PREFIX + HexFormat.of().formatHex(hashBytes);
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException("SHA-256 not available", e);
        }
    }

    /** 限流日志：同一类错误每 60 秒只打一次 */
    private void logThrottled(AtomicLong lastLogTime, String message, Exception e) {
        long now = System.currentTimeMillis();
        long last = lastLogTime.get();
        if (now - last > LOG_INTERVAL_MS && lastLogTime.compareAndSet(last, now)) {
            log.error(message, e);
        }
    }
}
