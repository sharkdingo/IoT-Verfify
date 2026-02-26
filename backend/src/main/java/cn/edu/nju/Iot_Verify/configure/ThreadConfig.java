package cn.edu.nju.Iot_Verify.configure;

import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.scheduling.concurrent.ThreadPoolTaskExecutor;

import java.util.concurrent.ThreadPoolExecutor;

@Configuration
public class ThreadConfig {

    private final ThreadPoolConfig threadPoolConfig;

    public ThreadConfig(ThreadPoolConfig threadPoolConfig) {
        this.threadPoolConfig = threadPoolConfig;
    }

    @Bean("chatExecutor")
    public ThreadPoolTaskExecutor chatExecutor() {
        ThreadPoolConfig.Pool pool = threadPoolConfig.getChat();
        return buildExecutor(pool.getCorePoolSize(), pool.getMaxPoolSize(),
                pool.getQueueCapacity(), "ai-chat-exec-", pool.getAwaitTerminationSeconds());
    }

    @Bean("verificationTaskExecutor")
    public ThreadPoolTaskExecutor verificationTaskExecutor() {
        ThreadPoolConfig.Pool pool = threadPoolConfig.getVerificationTask();
        return buildExecutor(pool.getCorePoolSize(), pool.getMaxPoolSize(),
                pool.getQueueCapacity(), "verification-task-", pool.getAwaitTerminationSeconds());
    }

    @Bean("syncVerificationExecutor")
    public ThreadPoolTaskExecutor syncVerificationExecutor() {
        ThreadPoolConfig.Pool pool = threadPoolConfig.getSyncVerification();
        return buildExecutor(pool.getCorePoolSize(), pool.getMaxPoolSize(),
                pool.getQueueCapacity(), "sync-verification-", pool.getAwaitTerminationSeconds());
    }

    @Bean("syncSimulationExecutor")
    public ThreadPoolTaskExecutor syncSimulationExecutor() {
        ThreadPoolConfig.Pool pool = threadPoolConfig.getSyncSimulation();
        return buildExecutor(pool.getCorePoolSize(), pool.getMaxPoolSize(),
                pool.getQueueCapacity(), "sync-simulation-", pool.getAwaitTerminationSeconds());
    }

    @Bean("simulationTaskExecutor")
    public ThreadPoolTaskExecutor simulationTaskExecutor() {
        ThreadPoolConfig.Pool pool = threadPoolConfig.getSimulationTask();
        return buildExecutor(pool.getCorePoolSize(), pool.getMaxPoolSize(),
                pool.getQueueCapacity(), "simulation-task-", pool.getAwaitTerminationSeconds());
    }

    private ThreadPoolTaskExecutor buildExecutor(int corePoolSize,
                                                 int maxPoolSize,
                                                 int queueCapacity,
                                                 String threadNamePrefix,
                                                 int awaitTerminationSeconds) {
        ThreadPoolTaskExecutor executor = new ThreadPoolTaskExecutor();
        executor.setCorePoolSize(corePoolSize);
        executor.setMaxPoolSize(maxPoolSize);
        executor.setQueueCapacity(queueCapacity);
        executor.setThreadNamePrefix(threadNamePrefix);
        executor.setRejectedExecutionHandler(new ThreadPoolExecutor.AbortPolicy());
        executor.setWaitForTasksToCompleteOnShutdown(true);
        executor.setAwaitTerminationSeconds(awaitTerminationSeconds);
        executor.initialize();
        return executor;
    }
}
