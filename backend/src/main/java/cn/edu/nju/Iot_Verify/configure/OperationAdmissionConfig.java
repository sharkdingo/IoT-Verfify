package cn.edu.nju.Iot_Verify.configure;

import jakarta.validation.constraints.Max;
import jakarta.validation.constraints.Min;
import lombok.Data;
import org.springframework.boot.context.properties.ConfigurationProperties;
import org.springframework.context.annotation.Configuration;
import org.springframework.validation.annotation.Validated;

@Data
@Validated
@Configuration
@ConfigurationProperties(prefix = "security.operation-admission")
public class OperationAdmissionConfig {

    @Min(1000)
    @Max(600000)
    private long leaseHeartbeatMs = 30000;
}
