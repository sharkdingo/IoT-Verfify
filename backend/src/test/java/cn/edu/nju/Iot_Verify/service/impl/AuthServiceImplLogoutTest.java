package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.service.TokenBlacklistService;
import cn.edu.nju.Iot_Verify.service.UserService;
import cn.edu.nju.Iot_Verify.util.JwtUtil;
import cn.edu.nju.Iot_Verify.util.mapper.UserMapper;
import io.jsonwebtoken.ExpiredJwtException;
import io.jsonwebtoken.MalformedJwtException;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.extension.ExtendWith;
import org.mockito.Mock;
import org.mockito.junit.jupiter.MockitoExtension;
import org.springframework.security.crypto.password.PasswordEncoder;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.Mockito.*;

@ExtendWith(MockitoExtension.class)
class AuthServiceImplLogoutTest {

    @Mock private UserService userService;
    @Mock private JwtUtil jwtUtil;
    @Mock private PasswordEncoder passwordEncoder;
    @Mock private TokenBlacklistService tokenBlacklistService;
    @Mock private UserMapper userMapper;
    @Mock private DeviceTemplateService deviceTemplateService;

    private AuthServiceImpl authService;

    @BeforeEach
    void setUp() {
        authService = new AuthServiceImpl(
                userService, jwtUtil, passwordEncoder,
                tokenBlacklistService, userMapper, deviceTemplateService
        );
    }

    // --- 正常登出 ---

    @Test
    void logout_validToken_blacklists() {
        when(jwtUtil.getExpirationSeconds("valid-token")).thenReturn(3600L);

        authService.logout(1L, "Bearer valid-token");

        verify(tokenBlacklistService).blacklist("valid-token", 3600L);
    }

    // --- userId 为 null ---

    @Test
    void logout_nullUserId_throwsUnauthorized() {
        assertThrows(UnauthorizedException.class, () -> authService.logout(null, "Bearer token"));
        verifyNoInteractions(tokenBlacklistService);
    }

    // --- 无 Authorization header ---

    @Test
    void logout_noAuthHeader_succeeds() {
        assertDoesNotThrow(() -> authService.logout(1L, null));
        verifyNoInteractions(tokenBlacklistService);
    }

    @Test
    void logout_nonBearerHeader_succeeds() {
        assertDoesNotThrow(() -> authService.logout(1L, "Basic abc123"));
        verifyNoInteractions(tokenBlacklistService);
    }

    // --- JwtException 降级 ---

    @Test
    void logout_expiredToken_doesNotThrow() {
        when(jwtUtil.getExpirationSeconds(anyString()))
                .thenThrow(new ExpiredJwtException(null, null, "expired"));

        assertDoesNotThrow(() -> authService.logout(1L, "Bearer expired-token"));
        verifyNoInteractions(tokenBlacklistService);
    }

    @Test
    void logout_malformedToken_doesNotThrow() {
        when(jwtUtil.getExpirationSeconds(anyString()))
                .thenThrow(new MalformedJwtException("bad token"));

        assertDoesNotThrow(() -> authService.logout(1L, "Bearer bad-token"));
        verifyNoInteractions(tokenBlacklistService);
    }

    // --- 非 JwtException 不被吞掉 ---

    @Test
    void logout_runtimeException_propagates() {
        when(jwtUtil.getExpirationSeconds(anyString()))
                .thenThrow(new RuntimeException("unexpected bug"));

        assertThrows(RuntimeException.class, () -> authService.logout(1L, "Bearer some-token"));
        verifyNoInteractions(tokenBlacklistService);
    }
}
