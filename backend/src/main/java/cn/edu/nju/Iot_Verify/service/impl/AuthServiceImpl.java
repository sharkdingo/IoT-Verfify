package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.auth.AuthResponseDto;
import cn.edu.nju.Iot_Verify.dto.auth.LoginRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.RegisterRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.RegisterResponseDto;
import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.service.AuthService;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import cn.edu.nju.Iot_Verify.service.TokenBlacklistService;
import cn.edu.nju.Iot_Verify.service.UserService;
import cn.edu.nju.Iot_Verify.util.JwtUtil;
import cn.edu.nju.Iot_Verify.util.mapper.UserMapper;
import lombok.RequiredArgsConstructor;
import lombok.extern.slf4j.Slf4j;
import org.springframework.security.crypto.password.PasswordEncoder;
import org.springframework.stereotype.Service;

@Slf4j
@Service
@RequiredArgsConstructor
public class AuthServiceImpl implements AuthService {

    private final UserService userService;
    private final JwtUtil jwtUtil;
    private final PasswordEncoder passwordEncoder;
    private final TokenBlacklistService tokenBlacklistService;
    private final UserMapper userMapper;
    private final DeviceTemplateService deviceTemplateService;

    @Override
    public RegisterResponseDto register(RegisterRequestDto request) {
        UserPo user = userService.register(
                request.getPhone(),
                request.getUsername(),
                request.getPassword()
        );

        // 注册成功后自动加载默认设备模板
        try {
            int count = deviceTemplateService.initDefaultTemplates(user.getId());
            log.info("Loaded {} default templates for new user {}", count, user.getId());
        } catch (Exception e) {
            log.warn("Failed to load default templates for user {}, registration still succeeds", user.getId(), e);
        }

        return userMapper.toRegisterResponseDto(user);
    }

    @Override
    public AuthResponseDto login(LoginRequestDto request) {
        UserPo user = userService.findByPhone(request.getPhone())
                .orElseThrow(UnauthorizedException::invalidCredentials);

        if (!passwordEncoder.matches(request.getPassword(), user.getPassword())) {
            throw UnauthorizedException.invalidCredentials();
        }

        String token = jwtUtil.generateToken(user.getId(), user.getPhone());
        return userMapper.toAuthResponseDto(user, token);
    }

    @Override
    public void logout(Long userId, String authHeader) {
        if (userId == null) {
            throw UnauthorizedException.missingToken();
        }

        if (authHeader != null && authHeader.startsWith("Bearer ")) {
            String token = authHeader.substring(7);
            long expirationSeconds = jwtUtil.getExpirationSeconds(token);
            tokenBlacklistService.blacklist(token, expirationSeconds);
        }
    }
}
