package cn.edu.nju.Iot_Verify.configure;

import lombok.Data;
import org.springframework.boot.context.properties.ConfigurationProperties;
import org.springframework.context.annotation.Configuration;

/**
 * NuSMV 配置
 */
@Data
@Configuration
@ConfigurationProperties(prefix = "nusmv")
public class NusmvConfig {
    
    /**
     * NuSMV 可执行文件路径
     */
    private String path = "/usr/bin/NuSMV";
    
    /**
     * NuSMV 命令前缀
     */
    private String commandPrefix = "";
    
    /**
     * 执行超时时间（毫秒）
     * 默认 120000ms (2分钟)
     */
    private long timeoutMs = 120000;
    
    /**
     * 是否启用攻击模式
     */
    private boolean attackEnabled = false;
}
