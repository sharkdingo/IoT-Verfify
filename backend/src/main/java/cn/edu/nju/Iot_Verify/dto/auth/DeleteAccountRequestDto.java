package cn.edu.nju.Iot_Verify.dto.auth;

import jakarta.validation.constraints.NotBlank;
import lombok.Data;

@Data
public class DeleteAccountRequestDto {

    @NotBlank(message = "Password is required")
    private String password;

    @NotBlank(message = "Account confirmation is required")
    private String confirmation;
}
