package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.auth.AuthResponseDto;
import cn.edu.nju.Iot_Verify.dto.auth.DeleteAccountRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.LoginRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.RegisterRequestDto;

public interface AuthService {
    AuthResponseDto register(RegisterRequestDto request);
    AuthResponseDto login(LoginRequestDto request);
    void logout(Long userId, String authHeader);
    void deleteAccount(Long userId, String authHeader, DeleteAccountRequestDto request);
}
