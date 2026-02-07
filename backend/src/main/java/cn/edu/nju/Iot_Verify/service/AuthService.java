package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.auth.AuthResponseDto;
import cn.edu.nju.Iot_Verify.dto.auth.LoginRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.RegisterRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.RegisterResponseDto;

public interface AuthService {
    RegisterResponseDto register(RegisterRequestDto request);
    AuthResponseDto login(LoginRequestDto request);
    void logout(Long userId, String authHeader);
}
