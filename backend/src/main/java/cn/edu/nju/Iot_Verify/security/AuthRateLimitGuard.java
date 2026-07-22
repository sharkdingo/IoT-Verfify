package cn.edu.nju.Iot_Verify.security;

import cn.edu.nju.Iot_Verify.exception.AuthRateLimitException;
import cn.edu.nju.Iot_Verify.util.UsernameNormalizer;
import jakarta.servlet.http.HttpServletRequest;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.stereotype.Component;

import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;
import java.security.NoSuchAlgorithmException;
import java.time.Duration;
import java.util.Base64;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

/** Bounds valid authentication attempts by account and by source without coupling users behind one NAT. */
@Component
public class AuthRateLimitGuard {

    private final int loginAccountLimit;
    private final int registerPhoneLimit;
    private final int loginSourceLimit;
    private final int registerSourceLimit;
    private final Map<String, Window> windows = new ConcurrentHashMap<>();
    private final AtomicLong requests = new AtomicLong();

    public AuthRateLimitGuard(
            @Value("${security.auth-rate-limit.login-per-minute:10}") int loginAccountLimit,
            @Value("${security.auth-rate-limit.register-per-hour:5}") int registerPhoneLimit,
            @Value("${security.auth-rate-limit.source-login-per-minute:120}") int loginSourceLimit,
            @Value("${security.auth-rate-limit.source-register-per-hour:60}") int registerSourceLimit) {
        this.loginAccountLimit = Math.max(1, loginAccountLimit);
        this.registerPhoneLimit = Math.max(1, registerPhoneLimit);
        this.loginSourceLimit = Math.max(this.loginAccountLimit, loginSourceLimit);
        this.registerSourceLimit = Math.max(this.registerPhoneLimit, registerSourceLimit);
    }

    public void checkLogin(String identifier, HttpServletRequest request) {
        check("login", normalizedIdentity(identifier), sourceAddress(request),
                loginAccountLimit, loginSourceLimit, Duration.ofMinutes(1));
    }

    public void checkRegistration(String phone, HttpServletRequest request) {
        check("register", normalizedIdentity(phone), sourceAddress(request),
                registerPhoneLimit, registerSourceLimit, Duration.ofHours(1));
    }

    private void check(String operation,
                       String identity,
                       String source,
                       int identityLimit,
                       int sourceLimit,
                       Duration duration) {
        long now = System.currentTimeMillis();
        long windowMs = duration.toMillis();
        Decision sourceDecision = consume(
                operation + ":source:" + source, sourceLimit, now, windowMs);
        if ((requests.incrementAndGet() & 1023L) == 0L) {
            windows.entrySet().removeIf(entry -> entry.getValue().expiresAt() <= now);
        }
        if (!sourceDecision.allowed()) {
            throw new AuthRateLimitException(operation, "SOURCE", sourceDecision.retryAfterSeconds());
        }
        Decision identityDecision = consume(
                operation + ":identity:" + digest(identity), identityLimit, now, windowMs);
        if (!identityDecision.allowed()) {
            throw new AuthRateLimitException(operation, "ACCOUNT", identityDecision.retryAfterSeconds());
        }
    }

    private Decision consume(String key, int limit, long now, long windowMs) {
        Window window = windows.compute(key, (ignored, current) -> {
            if (current == null || current.expiresAt() <= now) {
                return new Window(now + windowMs, 1);
            }
            return new Window(current.expiresAt(), current.count() + 1);
        });
        long retryAfter = Math.max(1, (window.expiresAt() - now + 999) / 1000);
        return new Decision(window.count() <= limit, retryAfter);
    }

    private String normalizedIdentity(String value) {
        return UsernameNormalizer.normalize(value);
    }

    private String sourceAddress(HttpServletRequest request) {
        String remoteAddress = request == null ? "unknown" : request.getRemoteAddr();
        if (request == null || !("127.0.0.1".equals(remoteAddress)
                || "0:0:0:0:0:0:0:1".equals(remoteAddress) || "::1".equals(remoteAddress))) {
            return remoteAddress == null || remoteAddress.isBlank() ? "unknown" : remoteAddress;
        }
        String proxyAddress = request.getHeader("X-Real-IP");
        if (proxyAddress == null) return remoteAddress;
        String normalized = proxyAddress.trim();
        return normalized.isEmpty() || normalized.length() > 128 ? remoteAddress : normalized;
    }

    private String digest(String value) {
        try {
            byte[] bytes = MessageDigest.getInstance("SHA-256")
                    .digest(value.getBytes(StandardCharsets.UTF_8));
            return Base64.getUrlEncoder().withoutPadding().encodeToString(bytes);
        } catch (NoSuchAlgorithmException e) {
            throw new IllegalStateException("SHA-256 is unavailable", e);
        }
    }

    private record Window(long expiresAt, int count) {
    }

    private record Decision(boolean allowed, long retryAfterSeconds) {
    }
}
