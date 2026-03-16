package cn.edu.nju.Iot_Verify.configure;

import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.Positive;
import lombok.Data;
import org.springframework.boot.context.properties.ConfigurationProperties;
import org.springframework.context.annotation.Configuration;
import org.springframework.validation.annotation.Validated;

@Data
@Validated
@Configuration
@ConfigurationProperties(prefix = "jwt")
public class JwtConfig {

    @NotBlank
    private String secret;

    @Positive
    private long expiration = 86400000;
}
