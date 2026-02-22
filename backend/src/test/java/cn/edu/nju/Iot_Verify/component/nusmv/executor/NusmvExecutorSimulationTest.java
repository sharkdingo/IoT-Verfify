package cn.edu.nju.Iot_Verify.component.nusmv.executor;

import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for NusmvExecutor simulation-related private methods.
 */
class NusmvExecutorSimulationTest {

    private NusmvExecutor executor;
    private Method extractSimulationTrace;

    @BeforeEach
    void setUp() throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setPath("/usr/bin/NuSMV");
        config.setCommandPrefix("");
        executor = new NusmvExecutor(config);

        extractSimulationTrace = NusmvExecutor.class
                .getDeclaredMethod("extractSimulationTrace", String.class);
        extractSimulationTrace.setAccessible(true);
    }

    @Test
    void extractSimulationTrace_withValidTrace_returnsTraceText() throws Exception {
        String rawOutput = "NuSMV > go\n"
                + "NuSMV > pick_state -r\n"
                + "Trace Description: Simulation\n"
                + "Trace Type: Simulation\n"
                + "  -> State: 1.1 <-\n"
                + "    device1.mode = on\n"
                + "  -> State: 1.2 <-\n"
                + "    device1.mode = off\n"
                + "NuSMV > quit\n";

        String result = (String) extractSimulationTrace.invoke(executor, rawOutput);

        assertNotNull(result);
        assertTrue(result.contains("State: 1.1"));
        assertTrue(result.contains("device1.mode = on"));
        assertTrue(result.contains("State: 1.2"));
        // NuSMV prompt lines should be filtered out
        assertFalse(result.contains("NuSMV >"));
    }

    @Test
    void extractSimulationTrace_noMarker_returnsNull() throws Exception {
        String rawOutput = "NuSMV > go\nsome random output\nNuSMV > quit\n";
        String result = (String) extractSimulationTrace.invoke(executor, rawOutput);
        assertNull(result);
    }

    @Test
    void extractSimulationTrace_nullInput_returnsNull() throws Exception {
        String result = (String) extractSimulationTrace.invoke(executor, (Object) null);
        assertNull(result);
    }

    @Test
    void extractSimulationTrace_emptyInput_returnsNull() throws Exception {
        String result = (String) extractSimulationTrace.invoke(executor, "");
        assertNull(result);
    }

    @Test
    void extractSimulationTrace_markerButOnlyPrompts_returnsNull() throws Exception {
        String rawOutput = "Trace Type: Simulation\nNuSMV > quit\n";
        String result = (String) extractSimulationTrace.invoke(executor, rawOutput);
        assertNull(result);
    }

    @Test
    void executeInteractiveSimulation_nullFile_returnsError() throws Exception {
        NusmvExecutor.SimulationOutput output = executor.executeInteractiveSimulation(null, 10);
        assertFalse(output.isSuccess());
        assertNotNull(output.getErrorMessage());
    }

    @Test
    void executeInteractiveSimulation_nonExistentFile_returnsError() throws Exception {
        java.io.File nonExistent = new java.io.File("/tmp/does_not_exist_" + System.nanoTime() + ".smv");
        NusmvExecutor.SimulationOutput output = executor.executeInteractiveSimulation(nonExistent, 10);
        assertFalse(output.isSuccess());
        assertTrue(output.getErrorMessage().contains("does not exist"));
    }
}