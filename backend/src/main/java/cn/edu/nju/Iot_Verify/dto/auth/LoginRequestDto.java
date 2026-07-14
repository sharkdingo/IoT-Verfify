package cn.edu.nju.Iot_Verify.dto.auth;

import jakarta.validation.constraints.NotBlank;
import lombok.Data;

@Data
public class LoginRequestDto {

    @NotBlank(message = "Account is required")
    private String identifier;

    @NotBlank(message = "Password is required")
    private String password;
}
