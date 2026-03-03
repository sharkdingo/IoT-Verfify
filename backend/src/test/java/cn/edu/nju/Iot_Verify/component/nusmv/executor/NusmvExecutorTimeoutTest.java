package cn.edu.nju.Iot_Verify.component.nusmv.executor;

import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.lang.reflect.Method;

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
}
