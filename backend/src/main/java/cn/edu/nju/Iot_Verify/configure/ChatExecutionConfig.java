package cn.edu.nju.Iot_Verify.configure;

import jakarta.validation.constraints.Min;
import lombok.Data;
import org.springframework.boot.context.properties.ConfigurationProperties;
import org.springframework.context.annotation.Configuration;
import org.springframework.validation.annotation.Validated;

@Data
@Configuration
@Validated
@ConfigurationProperties(prefix = "chat.execution")
public class ChatExecutionConfig {

    /**
     * Emergency runaway guard, not a normal task budget.
     */
    @Min(8)
    private int maxToolRounds = 64;

    /**
     * Stop only after this many consecutive rounds repeat the exact same calls and results.
     */
    @Min(1)
    private int maxStagnantRounds = 2;
}
