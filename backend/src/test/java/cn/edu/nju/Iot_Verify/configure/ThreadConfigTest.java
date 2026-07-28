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

    @Test
    void aLeakedInterruptFlagDoesNotReachTheNextTaskOnTheSameThread() throws Exception {
        // Cancellation paths re-arm the flag deliberately (FixStrategyUtils.preserveInterrupt,
        // AiToolManager), and FixContext.isExpired reports it, so whether the flag survives to the next
        // task decides whether an unrelated later request reports every strategy as timed out without
        // running. ThreadPoolExecutor.runWorker clears a worker's interrupt status before each task, so
        // it does not — this pins that guarantee, because the re-arming code depends on it and nothing
        // in this repo would otherwise catch the JDK behaviour changing or a custom pool replacing it.
        ThreadPoolConfig poolConfig = new ThreadPoolConfig();
        poolConfig.setFuzzTask(new ThreadPoolConfig.Pool(1, 1, 4, 1));
        ThreadPoolTaskExecutor executor = new ThreadConfig(poolConfig).fuzzTaskExecutor();
        CountDownLatch firstDone = new CountDownLatch(1);
        CountDownLatch secondDone = new CountDownLatch(1);
        AtomicBoolean sawLeakedInterrupt = new AtomicBoolean(false);

        try {
            executor.execute(() -> {
                Thread.currentThread().interrupt();
                firstDone.countDown();
            });
            assertTrue(firstDone.await(2, TimeUnit.SECONDS));

            executor.execute(() -> {
                sawLeakedInterrupt.set(Thread.currentThread().isInterrupted());
                secondDone.countDown();
            });
            assertTrue(secondDone.await(2, TimeUnit.SECONDS));

            assertFalse(sawLeakedInterrupt.get(),
                    "the interrupt flag leaked from a cancelled task into the next one");
        } finally {
            executor.shutdown();
        }
    }
}
