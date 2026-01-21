package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.*;
import cn.edu.nju.Iot_Verify.exception.UnauthorizedException;
import cn.edu.nju.Iot_Verify.po.UserPo;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.service.TokenBlacklistService;
import cn.edu.nju.Iot_Verify.service.UserService;
import cn.edu.nju.Iot_Verify.util.JwtUtil;
import jakarta.validation.Valid;
import lombok.RequiredArgsConstructor;
import org.springframework.security.crypto.password.PasswordEncoder;
import org.springframework.web.bind.annotation.*;

@RestController
@RequestMapping("/api/auth")
@RequiredArgsConstructor
public class AuthController {

    private final UserService userService;
    private final JwtUtil jwtUtil;
    private final PasswordEncoder passwordEncoder;
    private final TokenBlacklistService tokenBlacklistService;

    @PostMapping("/register")
    public Result<RegisterResponseDto> register(@Valid @RequestBody RegisterRequestDto request) {
        UserPo user = userService.register(request.getPhone(), request.getUsername(), request.getPassword());

        return Result.success(RegisterResponseDto.builder()
                .userId(user.getId())
                .phone(user.getPhone())
                .username(user.getUsername())
                .build());
    }

    @PostMapping("/login")
    public Result<AuthResponseDto> login(@Valid @RequestBody LoginRequestDto request) {
        UserPo user = userService.findByPhone(request.getPhone())
                .orElseThrow(UnauthorizedException::invalidCredentials);

        if (!passwordEncoder.matches(request.getPassword(), user.getPassword())) {
            throw UnauthorizedException.invalidCredentials();
        }

        String token = jwtUtil.generateToken(user.getId(), user.getPhone());

        return Result.success(AuthResponseDto.builder()
                .userId(user.getId())
                .phone(user.getPhone())
                .username(user.getUsername())
                .token(token)
                .build());
    }

    @PostMapping("/logout")
    public Result<Void> logout(@CurrentUser Long currentUser, @RequestHeader("Authorization") String authHeader) {
        if (currentUser == null) {
            throw UnauthorizedException.missingToken();
        }

        if (authHeader != null && authHeader.startsWith("Bearer ")) {
            String token = authHeader.substring(7);
            long expirationSeconds = jwtUtil.getExpirationSeconds(token);
            tokenBlacklistService.blacklist(token, expirationSeconds);
        }

        return Result.success();
    }
}
