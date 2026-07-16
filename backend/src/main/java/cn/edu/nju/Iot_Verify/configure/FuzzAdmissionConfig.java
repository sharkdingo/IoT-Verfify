package cn.edu.nju.Iot_Verify.configure;

import jakarta.validation.constraints.AssertTrue;
import jakarta.validation.constraints.Min;
import lombok.Data;
import org.springframework.boot.context.properties.ConfigurationProperties;
import org.springframework.context.annotation.Configuration;
import org.springframework.validation.annotation.Validated;

@Data
@Configuration
@Validated
@ConfigurationProperties(prefix = "fuzz.admission")
public class FuzzAdmissionConfig {

    @Min(1)
    private int maxActiveTasksPerUser = 2;

    @Min(1)
    private int maxStoredTasksPerUser = 100;

    @AssertTrue(message = "maxStoredTasksPerUser must be greater than or equal to maxActiveTasksPerUser")
    public boolean isStoredTaskLimitNotLessThanActiveTaskLimit() {
        return maxStoredTasksPerUser >= maxActiveTasksPerUser;
    }
}
