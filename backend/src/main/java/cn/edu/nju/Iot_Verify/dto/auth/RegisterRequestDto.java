package cn.edu.nju.Iot_Verify.dto.auth;

import cn.edu.nju.Iot_Verify.util.UsernameNormalizer;
import jakarta.validation.constraints.AssertTrue;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.Pattern;
import jakarta.validation.constraints.Size;
import lombok.Data;
import lombok.ToString;

@Data
public class RegisterRequestDto {

    @NotBlank(message = "Phone number is required")
    @Pattern(regexp = "^1[3-9]\\d{9}$", message = "Phone number format is invalid")
    private String phone;

    @NotBlank(message = "Username is required")
    @Size(max = 100, message = "Username must not exceed 100 characters before normalization")
    private String username;

    @NotBlank(message = "Password is required")
    @Size(min = 10, max = 64, message = "Password must be 10-64 characters")
    @ToString.Exclude
    private String password;

    @AssertTrue(message = "Password must not exceed 72 UTF-8 bytes")
    public boolean isPasswordWithinBcryptLimit() {
        return password == null || password.getBytes(java.nio.charset.StandardCharsets.UTF_8).length <= 72;
    }

    @AssertTrue(message = "Username must be 3-20 Unicode characters after trimming and must not contain control or format characters")
    public boolean isUsernameValidAfterNormalization() {
        return username == null || UsernameNormalizer.isValid(UsernameNormalizer.normalize(username));
    }
}
