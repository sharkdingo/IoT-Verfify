package cn.edu.nju.Iot_Verify.configure;

import jakarta.validation.constraints.Min;
import jakarta.validation.constraints.NotBlank;
import lombok.Data;
import org.springframework.boot.context.properties.ConfigurationProperties;
import org.springframework.context.annotation.Configuration;
import org.springframework.validation.annotation.Validated;

@Data
@Validated
@Configuration
@ConfigurationProperties(prefix = "volcengine.ark")
public class ArkAiConfig {

    @NotBlank
    private String apiKey;

    @NotBlank
    private String modelId;

    private String baseUrl = "https://ark.cn-beijing.volces.com";

    @Min(1)
    private int timeoutMinutes = 5;
}
