package cn.edu.nju.Iot_Verify.security;

import cn.edu.nju.Iot_Verify.exception.AuthRateLimitException;
import org.junit.jupiter.api.Test;
import org.springframework.mock.web.MockHttpServletRequest;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class AuthRateLimitGuardTest {

    @Test
    void usersBehindOneSourceDoNotShareTheLowAccountLimit() {
        AuthRateLimitGuard guard = new AuthRateLimitGuard(1, 1, 10, 10);
        MockHttpServletRequest request = request("203.0.113.10");

        assertDoesNotThrow(() -> guard.checkLogin("alice", request));
        assertDoesNotThrow(() -> guard.checkLogin("bob", request));
        AuthRateLimitException error = assertThrows(
                AuthRateLimitException.class, () -> guard.checkLogin("alice", request));

        assertEquals("ACCOUNT", error.getScope());
        assertEquals("AUTH_LOGIN_RATE_LIMIT_REACHED", error.getReasonCode());
    }

    @Test
    void highSourceLimitStillBoundsRotatingIdentifiers() {
        AuthRateLimitGuard guard = new AuthRateLimitGuard(1, 1, 2, 2);
        MockHttpServletRequest request = request("203.0.113.10");

        guard.checkLogin("alice", request);
        guard.checkLogin("bob", request);
        AuthRateLimitException error = assertThrows(
                AuthRateLimitException.class, () -> guard.checkLogin("carol", request));

        assertEquals("SOURCE", error.getScope());
        org.junit.jupiter.api.Assertions.assertTrue(error.getRetryAfterSeconds() >= 1);
    }

    @Test
    void sourceRejectionDoesNotConsumeTheRotatedIdentityLimit() {
        AuthRateLimitGuard guard = new AuthRateLimitGuard(1, 1, 1, 1);

        guard.checkLogin("alice", request("203.0.113.10"));
        AuthRateLimitException error = assertThrows(
                AuthRateLimitException.class,
                () -> guard.checkLogin("bob", request("203.0.113.10")));

        assertEquals("SOURCE", error.getScope());
        assertDoesNotThrow(() -> guard.checkLogin("bob", request("203.0.113.11")));
    }

    @Test
    void loopbackProxyUsesOverwrittenRealIp() {
        AuthRateLimitGuard guard = new AuthRateLimitGuard(10, 10, 1, 10);
        MockHttpServletRequest first = request("127.0.0.1");
        first.addHeader("X-Real-IP", "198.51.100.10");
        MockHttpServletRequest second = request("127.0.0.1");
        second.addHeader("X-Real-IP", "198.51.100.11");

        assertDoesNotThrow(() -> guard.checkLogin("alice", first));
        assertDoesNotThrow(() -> guard.checkLogin("alice", second));
    }

    private MockHttpServletRequest request(String address) {
        MockHttpServletRequest request = new MockHttpServletRequest();
        request.setRemoteAddr(address);
        return request;
    }
}
