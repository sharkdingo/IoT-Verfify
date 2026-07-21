package cn.edu.nju.Iot_Verify.controller;

import cn.edu.nju.Iot_Verify.dto.Result;
import cn.edu.nju.Iot_Verify.dto.auth.AuthResponseDto;
import cn.edu.nju.Iot_Verify.dto.auth.DeleteAccountRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.LoginRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.RegisterRequestDto;
import cn.edu.nju.Iot_Verify.security.CurrentUser;
import cn.edu.nju.Iot_Verify.security.AuthRateLimitGuard;
import cn.edu.nju.Iot_Verify.service.AuthService;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.validation.Valid;
import lombok.RequiredArgsConstructor;
import org.springframework.validation.annotation.Validated;
import org.springframework.web.bind.annotation.*;

@Validated
@RestController
@RequestMapping("/api/auth")
@RequiredArgsConstructor
public class AuthController {

    private final AuthService authService;
    private final AuthRateLimitGuard authRateLimitGuard;

    @PostMapping("/register")
    public Result<AuthResponseDto> register(
            @Valid @RequestBody RegisterRequestDto request,
            HttpServletRequest httpRequest) {
        authRateLimitGuard.checkRegistration(request.getPhone(), httpRequest);
        return Result.success(authService.register(request));
    }

    @PostMapping("/login")
    public Result<AuthResponseDto> login(
            @Valid @RequestBody LoginRequestDto request,
            HttpServletRequest httpRequest) {
        authRateLimitGuard.checkLogin(request.getIdentifier(), httpRequest);
        return Result.success(authService.login(request));
    }

    @PostMapping("/logout")
    public Result<Void> logout(@CurrentUser Long userId, @RequestHeader("Authorization") String authHeader) {
        authService.logout(userId, authHeader);
        return Result.success();
    }

    @DeleteMapping("/account")
    public Result<Void> deleteAccount(
            @CurrentUser Long userId,
            @RequestHeader("Authorization") String authHeader,
            @Valid @RequestBody DeleteAccountRequestDto request) {
        authService.deleteAccount(userId, authHeader, request);
        return Result.success();
    }
}
