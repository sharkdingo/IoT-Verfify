package cn.edu.nju.Iot_Verify.component.nusmv.executor;

import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.lang.reflect.Method;
import java.lang.reflect.Field;
import java.io.File;
import java.nio.file.Files;
import java.util.concurrent.Semaphore;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests that NuSMV execution timeout is sourced exclusively from NusmvConfig
 * (which is bound to application.yaml / environment variables via Spring).
 */
class NusmvExecutorTimeoutTest {

    private long invokeGetTimeout(NusmvExecutor executor) throws Exception {
        Method method = NusmvExecutor.class.getDeclaredMethod("getTimeout");
        method.setAccessible(true);
        return (long) method.invoke(executor);
    }

    @Test
    void getTimeout_returnsConfigValue() throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setTimeoutMs(60000);

        NusmvExecutor executor = new NusmvExecutor(config);

        long timeout = invokeGetTimeout(executor);
        assertEquals(60000, timeout);
    }

    @ParameterizedTest
    @ValueSource(longs = {100, 5000, 120000, 300000})
    void getTimeout_reflectsConfigChanges(long configuredTimeout) throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setTimeoutMs(configuredTimeout);

        NusmvExecutor executor = new NusmvExecutor(config);

        assertEquals(configuredTimeout, invokeGetTimeout(executor));
    }

    @Test
    void configDefault_isPositive() {
        NusmvConfig config = new NusmvConfig();
        assertTrue(config.getTimeoutMs() > 0,
                "NusmvConfig default timeout must be positive");
    }

    @Test
    void expiredCallerBudget_doesNotStartNuSMVOrChangePermitCount() throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setMaxConcurrent(1);
        NusmvExecutor executor = new NusmvExecutor(config);
        File model = Files.createTempFile("expired-fix", ".smv").toFile();

        NusmvExecutor.NusmvResult result = executor.execute(model, 0);

        assertFalse(result.isSuccess());
        assertTrue(result.getErrorMessage().contains("deadline expired"));
        Field semaphoreField = NusmvExecutor.class.getDeclaredField("executionSemaphore");
        semaphoreField.setAccessible(true);
        assertNull(semaphoreField.get(executor), "an expired call must not initialize or acquire the semaphore");
        assertTrue(model.delete());
    }

    @Test
    void failedPermitAcquisition_doesNotReleaseAnUnacquiredPermit() throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setMaxConcurrent(1);
        config.setAcquirePermitTimeoutMs(1);
        NusmvExecutor executor = new NusmvExecutor(config);
        Field semaphoreField = NusmvExecutor.class.getDeclaredField("executionSemaphore");
        semaphoreField.setAccessible(true);
        Semaphore occupied = new Semaphore(0, true);
        semaphoreField.set(executor, occupied);
        File model = Files.createTempFile("busy-fix", ".smv").toFile();

        NusmvExecutor.NusmvResult result = executor.execute(model, 1);

        assertFalse(result.isSuccess());
        assertEquals(0, occupied.availablePermits(), "a busy call must not create a phantom permit");
        assertTrue(model.delete());
    }
}
