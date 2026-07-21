package cn.edu.nju.Iot_Verify.dto.auth;

import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.Size;
import lombok.Data;

@Data
public class DeleteAccountRequestDto {

    @NotBlank(message = "Password is required")
    @Size(max = 128, message = "Password must not exceed 128 characters")
    private String password;

    @NotBlank(message = "Account confirmation is required")
    @Size(max = 100, message = "Account confirmation must not exceed 100 characters")
    private String confirmation;
}
