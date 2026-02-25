package cn.edu.nju.Iot_Verify.configure;

import jakarta.validation.Valid;
import jakarta.validation.constraints.AssertTrue;
import jakarta.validation.constraints.Min;
import jakarta.validation.constraints.NotNull;
import lombok.Data;
import org.springframework.boot.context.properties.ConfigurationProperties;
import org.springframework.context.annotation.Configuration;
import org.springframework.validation.annotation.Validated;

@Data
@Configuration
@Validated
@ConfigurationProperties(prefix = "thread-pool")
public class ThreadPoolConfig {

    @Valid
    @NotNull
    private Pool chat = new Pool(10, 50, 200, 30);
    @Valid
    @NotNull
    private Pool verificationTask = new Pool(5, 20, 100, 60);
    @Valid
    @NotNull
    private Pool syncVerification = new Pool(4, 4, 100, 30);
    @Valid
    @NotNull
    private Pool syncSimulation = new Pool(4, 4, 100, 30);
    @Valid
    @NotNull
    private Pool simulationTask = new Pool(5, 20, 100, 60);

    @Data
    public static class Pool {
        @Min(1)
        private int corePoolSize;
        @Min(1)
        private int maxPoolSize;
        @Min(0)
        private int queueCapacity;
        @Min(0)
        private int awaitTerminationSeconds;

        public Pool() {
        }

        public Pool(int corePoolSize, int maxPoolSize, int queueCapacity, int awaitTerminationSeconds) {
            this.corePoolSize = corePoolSize;
            this.maxPoolSize = maxPoolSize;
            this.queueCapacity = queueCapacity;
            this.awaitTerminationSeconds = awaitTerminationSeconds;
        }

        @AssertTrue(message = "corePoolSize must be less than or equal to maxPoolSize")
        public boolean isCorePoolSizeNotGreaterThanMaxPoolSize() {
            return corePoolSize <= maxPoolSize;
        }
    }
}
