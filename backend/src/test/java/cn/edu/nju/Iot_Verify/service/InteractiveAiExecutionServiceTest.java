package cn.edu.nju.Iot_Verify.service;

import cn.edu.nju.Iot_Verify.dto.model.InteractiveOperationStage;
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

class InteractiveAiExecutionServiceTest {

    private ThreadPoolTaskExecutor executor;
    private InteractiveAiExecutionService service;

    @BeforeEach
    void setUp() {
        executor = new ThreadPoolTaskExecutor();
        executor.setCorePoolSize(1);
        executor.setMaxPoolSize(1);
        executor.setQueueCapacity(1);
        executor.initialize();
        service = new InteractiveAiExecutionService(executor);
    }

    @AfterEach
    void tearDown() {
        executor.shutdown();
    }

    @Test
    void cancel_interruptsTheTrackedServerTask() throws Exception {
        CountDownLatch started = new CountDownLatch(1);
        CountDownLatch interrupted = new CountDownLatch(1);
        CompletableFuture<Void> request = CompletableFuture.runAsync(() -> {
            try {
                service.execute(1L, "request-123", () -> {
                    started.countDown();
                    try {
                        Thread.sleep(30_000);
                    } catch (InterruptedException e) {
                        interrupted.countDown();
                        Thread.currentThread().interrupt();
                    }
                    return null;
                });
            } catch (ServiceUnavailableException expected) {
                // Cancellation is surfaced to the waiting HTTP request as a terminal service response.
            }
        });

        assertTrue(started.await(2, TimeUnit.SECONDS));
        assertTrue(service.cancel(1L, "request-123"));
        request.get(2, TimeUnit.SECONDS);
        assertTrue(interrupted.await(2, TimeUnit.SECONDS));
    }

    @Test
    void statusReportsTheServerObservedStageWhileRunning() throws Exception {
        CountDownLatch started = new CountDownLatch(1);
        CountDownLatch releaseProvider = new CountDownLatch(1);
        CompletableFuture<Void> request = CompletableFuture.runAsync(() ->
                service.execute(1L, "request-123", () -> {
                    started.countDown();
                    releaseProvider.await();
                    return null;
                }));

        try {
            assertTrue(started.await(2, TimeUnit.SECONDS));
            service.markStage(1L, "request-123", InteractiveOperationStage.REQUESTING_MODEL);

            var status = service.getStatus(1L, "request-123");
            assertEquals("RUNNING", status.getState());
            assertEquals(InteractiveOperationStage.REQUESTING_MODEL, status.getStage());
            assertTrue(status.getElapsedMs() >= 0);
        } finally {
            releaseProvider.countDown();
            request.get(2, TimeUnit.SECONDS);
        }
    }

    @Test
    void completedStatusRemainsAvailableForTheFinalPollingTick() {
        service.execute(1L, "request-123", () -> {
            service.markStage(1L, "request-123", InteractiveOperationStage.VALIDATING_RESULT);
            return null;
        });

        var status = service.getStatus(1L, "request-123");
        assertEquals("FINISHED", status.getState());
        assertEquals(InteractiveOperationStage.VALIDATING_RESULT, status.getStage());
    }

    @Test
    void acceptsTheSameRequestIdCharactersAsTheControllerContract() {
        assertDoesNotThrow(() -> service.execute(1L, "request.v1:part", () -> null));
    }

    @Test
    void cancel_keepsUserAdmissionUntilInterruptIgnoringProviderActuallyReturns() throws Exception {
        CountDownLatch started = new CountDownLatch(1);
        CountDownLatch releaseProvider = new CountDownLatch(1);
        CountDownLatch providerReturned = new CountDownLatch(1);
        CompletableFuture<Void> request = CompletableFuture.runAsync(() -> {
            try {
                service.execute(1L, "request-123", () -> {
                    started.countDown();
                    while (releaseProvider.getCount() > 0) {
                        try {
                            releaseProvider.await(50, TimeUnit.MILLISECONDS);
                        } catch (InterruptedException ignored) {
                            // Simulate a provider call that does not stop when its Java thread is interrupted.
                        }
                    }
                    providerReturned.countDown();
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

            assertThrows(ServiceUnavailableException.class,
                    () -> service.execute(1L, "request-456", () -> null));

            releaseProvider.countDown();
            assertTrue(providerReturned.await(2, TimeUnit.SECONDS));
            awaitUserAdmissionRelease();
        } finally {
            releaseProvider.countDown();
        }
    }

    @Test
    void cancel_beforeStartRemovesQueuedWorkWithoutInvokingProvider() throws Exception {
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

        AtomicBoolean providerCalled = new AtomicBoolean(false);
        CompletableFuture<Void> request = CompletableFuture.runAsync(() -> {
            try {
                service.execute(1L, "request-123", () -> {
                    providerCalled.set(true);
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
            assertDoesNotThrow(() -> service.execute(1L, "request-456", () -> null));
        } finally {
            releaseWorker.countDown();
        }
        assertFalse(providerCalled.get());
    }

    private void awaitQueuedTask() throws Exception {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(2);
        while (executor.getThreadPoolExecutor().getQueue().isEmpty()) {
            if (System.nanoTime() >= deadline) {
                throw new AssertionError("Timed out waiting for queued recommendation");
            }
            Thread.yield();
        }
    }

    private void awaitUserAdmissionRelease() throws Exception {
        long deadline = System.nanoTime() + TimeUnit.SECONDS.toNanos(2);
        while (true) {
            try {
                assertDoesNotThrow(() -> service.execute(1L, "request-456", () -> null));
                return;
            } catch (AssertionError error) {
                if (System.nanoTime() >= deadline) throw error;
                Thread.yield();
            }
        }
    }
}
