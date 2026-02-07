package cn.edu.nju.Iot_Verify.dto.auth;

import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.Pattern;
import jakarta.validation.constraints.Size;
import lombok.Data;

@Data
public class RegisterRequestDto {

    @NotBlank(message = "Phone number is required")
    @Pattern(regexp = "^1[3-9]\\d{9}$", message = "Phone number format is invalid")
    private String phone;

    @NotBlank(message = "Username is required")
    @Size(min = 3, max = 20, message = "Username must be 3-20 characters")
    private String username;

    @NotBlank(message = "Password is required")
    @Size(min = 6, max = 20, message = "Password must be 6-20 characters")
    private String password;
}
