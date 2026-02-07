package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.auth.AuthResponseDto;
import cn.edu.nju.Iot_Verify.dto.auth.LoginRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.RegisterRequestDto;
import cn.edu.nju.Iot_Verify.dto.auth.RegisterResponseDto;
import cn.edu.nju.Iot_Verify.po.UserPo;
import org.springframework.stereotype.Component;

/**
 * User PO 与 Auth DTOs 之间的转换映射器
 */
@Component
public class UserMapper {

    /**
     * RegisterRequestDto -> UserPo
     */
    public UserPo toUserPo(RegisterRequestDto registerRequestDto) {
        if (registerRequestDto == null) {
            return null;
        }
        UserPo po = new UserPo();
        po.setPhone(registerRequestDto.getPhone());
        po.setUsername(registerRequestDto.getUsername());
        po.setPassword(registerRequestDto.getPassword());
        return po;
    }

    /**
     * UserPo -> RegisterResponseDto
     */
    public RegisterResponseDto toRegisterResponseDto(UserPo userPo) {
        if (userPo == null) {
            return null;
        }
        RegisterResponseDto dto = new RegisterResponseDto();
        dto.setUserId(userPo.getId());
        dto.setPhone(userPo.getPhone());
        dto.setUsername(userPo.getUsername());
        return dto;
    }

    /**
     * UserPo -> AuthResponseDto (登录成功返回)
     */
    public AuthResponseDto toAuthResponseDto(UserPo userPo, String token) {
        if (userPo == null) {
            return null;
        }
        AuthResponseDto dto = new AuthResponseDto();
        dto.setUserId(userPo.getId());
        dto.setPhone(userPo.getPhone());
        dto.setUsername(userPo.getUsername());
        dto.setToken(token);
        return dto;
    }

    /**
     * LoginRequestDto -> UserPo (用于验证密码)
     */
    public UserPo toUserPoFromLogin(LoginRequestDto loginRequestDto) {
        if (loginRequestDto == null) {
            return null;
        }
        UserPo po = new UserPo();
        po.setPhone(loginRequestDto.getPhone());
        po.setPassword(loginRequestDto.getPassword());
        return po;
    }
}
