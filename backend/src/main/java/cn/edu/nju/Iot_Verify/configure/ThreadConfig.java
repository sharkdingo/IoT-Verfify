package cn.edu.nju.Iot_Verify.configure;

import org.springframework.context.annotation.Bean;
import org.springframework.context.annotation.Configuration;
import org.springframework.scheduling.concurrent.ThreadPoolTaskExecutor;

import java.util.concurrent.Executor;
import java.util.concurrent.ThreadPoolExecutor;

@Configuration
public class ThreadConfig {

    @Bean("chatExecutor")
    public Executor chatExecutor() {
        ThreadPoolTaskExecutor executor = new ThreadPoolTaskExecutor();
        // 核心线程数：根据你的 CPU 核数设置，IO 密集型任务通常设为 CPU核数 * 2
        executor.setCorePoolSize(10);
        // 最大线程数：突发流量时的最大承载
        executor.setMaxPoolSize(50);
        // 队列容量：排队等候的任务数，设为有界防止内存溢出
        executor.setQueueCapacity(200);
        // 线程前缀，方便日志排查
        executor.setThreadNamePrefix("ai-chat-exec-");
        // 拒绝策略：队列满了直接抛异常，保护服务器不崩
        executor.setRejectedExecutionHandler(new ThreadPoolExecutor.AbortPolicy());

        executor.initialize();
        return executor;
    }
}