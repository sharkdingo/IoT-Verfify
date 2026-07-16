package cn.edu.nju.Iot_Verify.configure;

import org.junit.jupiter.api.Test;
import org.springframework.scheduling.concurrent.ThreadPoolTaskExecutor;

import java.util.concurrent.CountDownLatch;
import java.util.concurrent.FutureTask;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ThreadConfigTest {

    @Test
    void cancelledDecoratedFutureCanBePurgedFromTheExecutorQueue() throws Exception {
        ThreadPoolConfig poolConfig = new ThreadPoolConfig();
        poolConfig.setFuzzTask(new ThreadPoolConfig.Pool(1, 1, 2, 1));
        ThreadPoolTaskExecutor executor = new ThreadConfig(poolConfig).fuzzTaskExecutor();
        CountDownLatch blockerStarted = new CountDownLatch(1);
        CountDownLatch releaseBlocker = new CountDownLatch(1);
        AtomicBoolean queuedTaskRan = new AtomicBoolean(false);

        try {
            executor.execute(() -> {
                blockerStarted.countDown();
                try {
                    releaseBlocker.await();
                } catch (InterruptedException e) {
                    Thread.currentThread().interrupt();
                }
            });
            assertTrue(blockerStarted.await(2, TimeUnit.SECONDS));

            FutureTask<Void> queuedTask = new FutureTask<>(
                    () -> queuedTaskRan.set(true), null);
            executor.execute(queuedTask);
            assertEquals(1, executor.getQueueSize());

            assertTrue(queuedTask.cancel(false));
            executor.getThreadPoolExecutor().purge();

            assertEquals(0, executor.getQueueSize());
            assertFalse(queuedTaskRan.get());
        } finally {
            releaseBlocker.countDown();
            executor.shutdown();
        }
    }
}
