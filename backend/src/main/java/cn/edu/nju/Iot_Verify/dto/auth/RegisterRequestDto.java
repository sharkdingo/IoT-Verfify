package cn.edu.nju.Iot_Verify.dto.auth;

import cn.edu.nju.Iot_Verify.dto.RequestLimits;
import cn.edu.nju.Iot_Verify.util.UsernameNormalizer;
import jakarta.validation.constraints.AssertTrue;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.Pattern;
import jakarta.validation.constraints.Size;
import lombok.Data;
import lombok.ToString;

@Data
public class RegisterRequestDto {

    // The bounds come from `RequestLimits`, which the frontend mirrors, rather than being written out here.
    // They were literals at three sites — this DTO, `ValidationException`'s message, and `Landing.vue`'s
    // client-side check — so a change to any one of them left the others claiming the old rule.
    @NotBlank(message = "Phone number is required")
    @Pattern(regexp = RequestLimits.PHONE_PATTERN, message = "Phone number format is invalid")
    private String phone;

    @NotBlank(message = "Username is required")
    @Size(max = RequestLimits.MAX_USERNAME_LENGTH,
          message = "Username must not exceed 100 characters before normalization")
    private String username;

    @NotBlank(message = "Password is required")
    @Size(min = RequestLimits.MIN_PASSWORD_LENGTH, max = RequestLimits.MAX_PASSWORD_LENGTH,
          message = "Password must be 10-64 characters")
    @ToString.Exclude
    private String password;

    @AssertTrue(message = "Password must not exceed 72 UTF-8 bytes")
    public boolean isPasswordWithinBcryptLimit() {
        return password == null
                || password.getBytes(java.nio.charset.StandardCharsets.UTF_8).length
                        <= RequestLimits.MAX_PASSWORD_BCRYPT_BYTES;
    }

    @AssertTrue(message = "Username must be 3-20 Unicode characters after trimming and must not contain control or format characters")
    public boolean isUsernameValidAfterNormalization() {
        return username == null || UsernameNormalizer.isValid(UsernameNormalizer.normalize(username));
    }
}
