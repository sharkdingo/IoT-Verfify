package cn.edu.nju.Iot_Verify.configure;

import jakarta.validation.Valid;
import jakarta.validation.constraints.AssertTrue;
import jakarta.validation.constraints.Min;
import lombok.Data;
import org.springframework.boot.context.properties.ConfigurationProperties;
import org.springframework.context.annotation.Configuration;
import org.springframework.validation.annotation.Validated;

@Data
@Configuration
@Validated
@ConfigurationProperties(prefix = "async-task-admission")
public class AsyncTaskAdmissionConfig {

    @Valid
    private Limits verification = new Limits();

    @Valid
    private Limits simulation = new Limits();

    @Data
    public static class Limits {
        @Min(1)
        private int maxActiveTasksPerUser = 2;

        @Min(1)
        private int maxStoredTasksPerUser = 100;

        @AssertTrue(message = "maxStoredTasksPerUser must be greater than or equal to maxActiveTasksPerUser")
        public boolean isStoredTaskLimitNotLessThanActiveTaskLimit() {
            return maxStoredTasksPerUser >= maxActiveTasksPerUser;
        }
    }
}
