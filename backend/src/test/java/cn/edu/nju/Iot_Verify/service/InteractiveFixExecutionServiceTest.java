package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.model.InteractiveOperationStage;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.ServiceUnavailableException;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.springframework.scheduling.concurrent.ThreadPoolTaskExecutor;

import java.util.concurrent.CompletableFuture;
import java.util.concurrent.CountDownLatch;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicBoolean;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

class InteractiveFixExecutionServiceTest {

    private ThreadPoolTaskExecutor executor;
    private InteractiveFixExecutionService service;

    @BeforeEach
    void setUp() {
        executor = new ThreadPoolTaskExecutor();
        executor.setCorePoolSize(1);
        executor.setMaxPoolSize(1);
        executor.setQueueCapacity(1);
        executor.initialize();
        service = new InteractiveFixExecutionService(executor);
    }

    @AfterEach
    void tearDown() {
        executor.shutdown();
    }

    @Test
    void cancel_keepsRequestIdReservedUntilInterruptIgnoringSearchActuallyReturns() throws Exception {
        CountDownLatch started = new CountDownLatch(1);
        CountDownLatch releaseSearch = new CountDownLatch(1);
        CountDownLatch searchReturned = new CountDownLatch(1);
        CompletableFuture<Void> request = CompletableFuture.runAsync(() -> {
            try {
                service.execute(1L, "request-123", () -> {
                    started.countDown();
                    while (releaseSearch.getCount() > 0) {
                        try {
                            releaseSearch.await(50, TimeUnit.MILLISECONDS);
                        } catch (InterruptedException ignored) {
                            // Simulate an external checker that has not exited after interruption.
                        }
                    }
                    searchReturned.countDown();
                    return null;
                });
            } catch (ServiceUnavailableException expected) {
                // The waiting HTTP request is released as soon as cancellation is accepted.
            }
        });

        try {
            assertTrue(started.await(2, TimeUnit.SECONDS));
            assertTrue(service.cancel(1L, "request-123"));
            request.get(2, TimeUnit.SECONDS);

            assertThrows(BadRequestException.class,
                    () -> service.execute(1L, "request-123", () -> null));

            releaseSearch.countDown();
            assertTrue(searchReturned.await(2, TimeUnit.SECONDS));
            awaitRequestIdRelease();
        } finally {
            releaseSearch.countDown();
        }
    }

    @Test
    void statusReportsTheServerObservedStageWhileRunning() throws Exception {
        CountDownLatch started = new CountDownLatch(1);
        CountDownLatch releaseSearch = new CountDownLatch(1);
        CompletableFuture<Void> request = CompletableFuture.runAsync(() ->
                service.execute(1L, "request-123", () -> {
                    started.countDown();
                    releaseSearch.await();
                    return null;
                }));

        try {
            assertTrue(started.await(2, TimeUnit.SECONDS));
            service.markStage(1L, "request-123", InteractiveOperationStage.SEARCHING_AND_VERIFYING);

            var status = service.getStatus(1L, "request-123");
            assertEquals("RUNNING", status.getState());
            assertEquals(InteractiveOperationStage.SEARCHING_AND_VERIFYING, status.getStage());
            assertTrue(status.getElapsedMs() >= 0);
        } finally {
            releaseSearch.countDown();
            request.get(2, TimeUnit.SECONDS);
        }
    }

    @Test
    void completedStatusRemainsAvailableForTheFinalPollingTick() {
        service.execute(1L, "request-123", () -> {
            service.markStage(1L, "request-123", InteractiveOperationStage.FINALIZING);
            return null;
        });

        var status = service.getStatus(1L, "request-123");
        assertEquals("FINISHED", status.getState());
        assertEquals(InteractiveOperationStage.FINALIZING, status.getStage());
    }

    @Test
    void cancel_beforeStartRemovesQueuedWorkWithoutInvokingChecker() throws Exception {
        CountDownLatch workerStarted = new CountDownLatch(1);
        CountDownLatch releaseWorker = new CountDownLatch(1);
        executor.execute(() -> {
            workerStarted.countDown();
            try {
                releaseWorker.await();
            } catch (InterruptedException e) {
                Thread.currentThread().interrupt();
            }
        });
        assertTrue(workerStarted.await(2, TimeUnit.SECONDS));

        AtomicBoolean checkerCalled = new AtomicBoolean(false);
        CompletableFuture<Void> request = CompletableFuture.runAsync(() -> {
            try {
                service.execute(1L, "request-123", () -> {
                    checkerCalled.set(true);
                    return null;
                });
            } catch (ServiceUnavailableException expected) {
                // Cancellation releases the waiting HTTP request.
            }
        });

        try {
            awaitQueuedTask();
            assertTrue(service.cancel(1L, "request-123"));
            request.get(2, TimeUnit.SECONDS);
            releaseWorker.countDown();
            assertDoesNotThrow(() -> service.execute(1L, "request-123", () -> null));
        } finally {
            releaseWorker.countDown();
        }
        assertFalse(checkerCalled.get());
    }

    private void awaitQueuedTask() throws Exception {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(2);
        while (executor.getThreadPoolExecutor().getQueue().isEmpty()) {
            if (System.nanoTime() >= deadline) {
                throw new AssertionError("Timed out waiting for queued fix search");
            }
            Thread.yield();
        }
    }

    private void awaitRequestIdRelease() throws Exception {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(2);
        while (true) {
            try {
                assertDoesNotThrow(() -> service.execute(1L, "request-123", () -> null));
                return;
            } catch (AssertionError error) {
                if (System.nanoTime() >= deadline) throw error;
                Thread.yield();
            }
        }
    }
}
