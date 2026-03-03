package cn.edu.nju.Iot_Verify.configure;

import jakarta.validation.constraints.Min;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.Positive;
import lombok.Data;
import org.springframework.boot.context.properties.ConfigurationProperties;
import org.springframework.context.annotation.Configuration;
import org.springframework.validation.annotation.Validated;

/**
 * NuSMV 配置
 */
@Data
@Validated
@Configuration
@ConfigurationProperties(prefix = "nusmv")
public class NusmvConfig {

    /**
     * NuSMV 可执行文件路径（由 application.yaml nusmv.path 设置）
     */
    @NotBlank
    private String path;

    /**
     * NuSMV 命令前缀
     */
    private String commandPrefix = "";

    /**
     * 执行超时时间（毫秒）
     * 默认 120000ms (2分钟)，最小 100ms
     */
    @Min(100)
    private long timeoutMs = 120000;

    /**
     * NuSMV process global concurrency cap shared by verification/simulation.
     */
    @Min(1)
    private int maxConcurrent = 6;

    /**
     * Timeout for waiting NuSMV execution permit (ms).
     */
    @Positive
    private long acquirePermitTimeoutMs = 10000;
}
