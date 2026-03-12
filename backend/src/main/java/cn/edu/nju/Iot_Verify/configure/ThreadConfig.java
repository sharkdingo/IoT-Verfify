package cn.edu.nju.Iot_Verify.configure;

import cn.edu.nju.Iot_Verify.security.UserContextHolder;
import org.slf4j.MDC;
import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.core.task.TaskDecorator;
import org.springframework.lang.NonNull;
import org.springframework.scheduling.concurrent.ThreadPoolTaskExecutor;
import org.springframework.security.authentication.UsernamePasswordAuthenticationToken;
import org.springframework.security.core.Authentication;
import org.springframework.security.core.context.SecurityContext;
import org.springframework.security.core.context.SecurityContextHolder;

import java.util.ArrayList;
import java.util.Map;
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
        executor.setTaskDecorator(contextPropagatingDecorator());
        executor.initialize();
        return executor;
    }

    @NonNull
    private TaskDecorator contextPropagatingDecorator() {
        return runnable -> {
            Authentication auth = SecurityContextHolder.getContext().getAuthentication();
            Authentication authCopy = deepCopyAuthentication(auth);
            Long userId = UserContextHolder.getUserId();
            Map<String, String> mdcCtx = MDC.getCopyOfContextMap();
            return () -> {
                SecurityContext newCtx = SecurityContextHolder.createEmptyContext();
                if (authCopy != null) {
                    newCtx.setAuthentication(authCopy);
                }
                SecurityContextHolder.setContext(newCtx);
                if (userId != null) {
                    UserContextHolder.setUserId(userId);
                }
                if (mdcCtx != null) {
                    MDC.setContextMap(mdcCtx);
                }
                try {
                    runnable.run();
                } finally {
                    SecurityContextHolder.clearContext();
                    UserContextHolder.clear();
                    MDC.clear();
                }
            };
        };
    }

    private Authentication deepCopyAuthentication(Authentication auth) {
        if (auth == null) {
            return null;
        }
        UsernamePasswordAuthenticationToken copy = new UsernamePasswordAuthenticationToken(
                auth.getPrincipal(),
                auth.getCredentials(),
                new ArrayList<>(auth.getAuthorities()));
        copy.setDetails(auth.getDetails());
        return copy;
    }
}
