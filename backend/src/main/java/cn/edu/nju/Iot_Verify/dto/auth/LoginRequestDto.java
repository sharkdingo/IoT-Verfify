package cn.edu.nju.Iot_Verify.dto.auth;

import jakarta.validation.constraints.NotBlank;
import lombok.Data;

@Data
public class LoginRequestDto {

    @NotBlank(message = "Phone number is required")
    private String phone;

    @NotBlank(message = "Password is required")
    private String password;
}
