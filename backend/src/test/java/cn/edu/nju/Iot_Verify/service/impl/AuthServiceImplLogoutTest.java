package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.auth.AuthResponseDto;
import cn.edu.nju.Iot_Verify.dto.auth.LoginRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.RegisterRequestDto;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.repository.BoardLayoutRepository;
import cn.edu.nju.Iot_Verify.repository.BoardEnvironmentVariableRepository;
import cn.edu.nju.Iot_Verify.repository.ChatMessageRepository;
import cn.edu.nju.Iot_Verify.repository.ChatSessionRepository;
import cn.edu.nju.Iot_Verify.repository.DeviceNodeRepository;
import cn.edu.nju.Iot_Verify.repository.DeviceTemplateRepository;
import cn.edu.nju.Iot_Verify.repository.RuleRepository;
import cn.edu.nju.Iot_Verify.repository.SimulationTaskRepository;
import cn.edu.nju.Iot_Verify.repository.SimulationTraceRepository;
import cn.edu.nju.Iot_Verify.repository.SpecificationRepository;
import cn.edu.nju.Iot_Verify.repository.TraceRepository;
import cn.edu.nju.Iot_Verify.repository.UserRepository;
import cn.edu.nju.Iot_Verify.repository.VerificationTaskRepository;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.service.SimulationService;
import cn.edu.nju.Iot_Verify.service.TokenBlacklistService;
import cn.edu.nju.Iot_Verify.service.UserService;
import cn.edu.nju.Iot_Verify.service.VerificationService;
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

import java.util.Optional;

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
    @Mock private VerificationService verificationService;
    @Mock private SimulationService simulationService;
    @Mock private UserRepository userRepository;
    @Mock private BoardEnvironmentVariableRepository boardEnvironmentVariableRepository;
    @Mock private BoardLayoutRepository boardLayoutRepository;
    @Mock private ChatMessageRepository chatMessageRepository;
    @Mock private ChatSessionRepository chatSessionRepository;
    @Mock private DeviceNodeRepository deviceNodeRepository;
    @Mock private DeviceTemplateRepository deviceTemplateRepository;
    @Mock private RuleRepository ruleRepository;
    @Mock private SimulationTaskRepository simulationTaskRepository;
    @Mock private SimulationTraceRepository simulationTraceRepository;
    @Mock private SpecificationRepository specificationRepository;
    @Mock private TraceRepository traceRepository;
    @Mock private VerificationTaskRepository verificationTaskRepository;

    private AuthServiceImpl authService;

    @BeforeEach
    void setUp() {
        authService = new AuthServiceImpl(
                userService, jwtUtil, passwordEncoder,
                tokenBlacklistService, userMapper, deviceTemplateService,
                verificationService, simulationService, userRepository,
                boardEnvironmentVariableRepository,
                boardLayoutRepository, chatMessageRepository, chatSessionRepository,
                deviceNodeRepository, deviceTemplateRepository, ruleRepository,
                simulationTaskRepository, simulationTraceRepository, specificationRepository,
                traceRepository, verificationTaskRepository
        );
    }

    @Test
    void login_withUsername_whenPhoneNotFound_succeeds() {
        LoginRequestDto request = new LoginRequestDto();
        request.setIdentifier("alice");
        request.setPassword("Pass1234");
        UserPo user = UserPo.builder()
                .id(7L)
                .phone("13900000000")
                .username("alice")
                .password("encoded")
                .build();
        AuthResponseDto response = AuthResponseDto.builder()
                .userId(7L)
                .phone("13900000000")
                .username("alice")
                .token("jwt")
                .build();

        when(userService.findByPhone("alice")).thenReturn(Optional.empty());
        when(userService.findByUsername("alice")).thenReturn(Optional.of(user));
        when(passwordEncoder.matches("Pass1234", "encoded")).thenReturn(true);
        when(jwtUtil.generateToken(7L, "13900000000")).thenReturn("jwt");
        when(userMapper.toAuthResponseDto(user, "jwt")).thenReturn(response);

        AuthResponseDto result = authService.login(request);

        assertEquals("alice", result.getUsername());
        assertEquals("jwt", result.getToken());
        verify(userService).findByPhone("alice");
        verify(userService).findByUsername("alice");
    }

    @Test
    void register_whenDefaultCatalogCannotBeInitialized_doesNotReturnPartialSuccess() {
        RegisterRequestDto request = new RegisterRequestDto();
        request.setPhone("13900000000");
        request.setUsername("alice");
        request.setPassword("Pass1234");
        UserPo user = UserPo.builder().id(7L).phone(request.getPhone()).username(request.getUsername()).build();
        when(userService.register(request.getPhone(), request.getUsername(), request.getPassword()))
                .thenReturn(user);
        when(deviceTemplateService.initDefaultTemplates(7L)).thenReturn(0);

        assertThrows(InternalServerException.class, () -> authService.register(request));

        verify(userMapper, never()).toRegisterResponseDto(any());
    }

    @Test
    void register_whenDefaultCatalogLoadFails_propagatesFailure() {
        RegisterRequestDto request = new RegisterRequestDto();
        request.setPhone("13900000000");
        request.setUsername("alice");
        request.setPassword("Pass1234");
        UserPo user = UserPo.builder().id(7L).phone(request.getPhone()).username(request.getUsername()).build();
        when(userService.register(request.getPhone(), request.getUsername(), request.getPassword()))
                .thenReturn(user);
        when(deviceTemplateService.initDefaultTemplates(7L))
                .thenThrow(new InternalServerException("defaults invalid"));

        InternalServerException error = assertThrows(
                InternalServerException.class, () -> authService.register(request));

        assertEquals("defaults invalid", error.getMessage());
        verify(userMapper, never()).toRegisterResponseDto(any());
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
