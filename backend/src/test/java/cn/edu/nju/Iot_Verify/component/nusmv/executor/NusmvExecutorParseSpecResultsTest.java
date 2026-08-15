package cn.edu.nju.Iot_Verify.component.nusmv.executor;

import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

class NusmvExecutorParseSpecResultsTest {

    private NusmvExecutor executor;
    private Method parseSpecResults;

    @BeforeEach
    void setUp() throws Exception {
        NusmvConfig config = new NusmvConfig();
        config.setPath("/usr/bin/NuSMV");
        config.setCommandPrefix("");
        executor = new NusmvExecutor(config);

        parseSpecResults = NusmvExecutor.class
                .getDeclaredMethod("parseSpecResults", String.class);
        parseSpecResults.setAccessible(true);
    }

    @Test
    @SuppressWarnings("unchecked")
    void parseSpecResults_withNuSMV271Output_preservesOrderAndCounterexample() throws Exception {
        String output = "*** This is NuSMV 2.7.1\n"
                + "-- specification AG dev1.SwitchState = off  is false\n"
                + "-- as demonstrated by the following execution sequence\n"
                + "Trace Description: CTL Counterexample \n"
                + "Trace Type: Counterexample \n"
                + "  -> State: 1.1 <-\n"
                + "    dev1.SwitchState = on\n"
                + "    dev1.on_a = FALSE\n"
                + "-- specification AG dev1.SwitchState = on  is true\n";

        List<NusmvExecutor.SpecCheckResult> results =
                (List<NusmvExecutor.SpecCheckResult>) parseSpecResults.invoke(executor, output);

        assertEquals(2, results.size());
        assertEquals("AG dev1.SwitchState = off", results.get(0).getSpecExpression());
        assertFalse(results.get(0).isPassed());
        assertNotNull(results.get(0).getCounterexample());
        assertTrue(results.get(0).getCounterexample().contains("State: 1.1"));
        assertTrue(results.get(0).getCounterexample().contains("dev1.SwitchState = on"));
        assertFalse(results.get(0).getCounterexample().contains("AG dev1.SwitchState = on"));

        assertEquals("AG dev1.SwitchState = on", results.get(1).getSpecExpression());
        assertTrue(results.get(1).isPassed());
        assertNull(results.get(1).getCounterexample());
    }

    /**
     * The lasso marker must survive extraction even when it precedes the first state line.
     *
     * Verbatim shape from NuSMV 2.7.1 for `AF x` over a model that never sets `x`: when the loop entry is the
     * *initial* state, "-- Loop starts here" is printed above "-> State: 1.1 <-". Extraction started copying
     * only at the first state line, so the marker was dropped before `SmvTraceParser` could ever see it — and
     * the whole trace then read as a finite path whose last step simply showed no change.
     */
    @Test
    @SuppressWarnings("unchecked")
    void parseSpecResults_keepsLoopMarkerThatPrecedesTheFirstState() throws Exception {
        String output = "*** This is NuSMV 2.7.1\n"
                + "-- specification AF dev1.SwitchState = on  is false\n"
                + "-- as demonstrated by the following execution sequence\n"
                + "Trace Description: CTL Counterexample \n"
                + "Trace Type: Counterexample \n"
                + "  -- Loop starts here\n"
                + "  -> State: 1.1 <-\n"
                + "    dev1.SwitchState = off\n"
                + "  -> State: 1.2 <-\n";

        List<NusmvExecutor.SpecCheckResult> results =
                (List<NusmvExecutor.SpecCheckResult>) parseSpecResults.invoke(executor, output);

        assertEquals(1, results.size());
        String counterexample = results.get(0).getCounterexample();
        assertNotNull(counterexample);
        assertTrue(counterexample.contains("Loop starts here"),
                "the marker is the only record that this path is infinite");
        // It must still begin at the marker/state region, never at the surrounding prose.
        assertFalse(counterexample.contains("Trace Type"),
                "extraction must not widen to the trace header");
        assertTrue(counterexample.indexOf("Loop starts here") < counterexample.indexOf("State: 1.1"),
                "the marker keeps its position, since it names the state that follows it");
    }

    /** A marker with no state behind it must not turn an empty block into a non-empty counterexample. */
    @Test
    @SuppressWarnings("unchecked")
    void parseSpecResults_ignoresALoneLoopMarkerWithNoStates() throws Exception {
        String output = "*** This is NuSMV 2.7.1\n"
                + "-- specification AF dev1.SwitchState = on  is false\n"
                + "  -- Loop starts here\n";

        List<NusmvExecutor.SpecCheckResult> results =
                (List<NusmvExecutor.SpecCheckResult>) parseSpecResults.invoke(executor, output);

        assertEquals(1, results.size());
        assertNull(results.get(0).getCounterexample(),
                "a marker alone is not a trace");
    }

    @Test
    @SuppressWarnings("unchecked")
    void parseSpecResults_whenNoSpecLines_returnsEmptyList() throws Exception {
        List<NusmvExecutor.SpecCheckResult> results =
                (List<NusmvExecutor.SpecCheckResult>) parseSpecResults.invoke(executor, "NuSMV > no specs\n");

        assertTrue(results.isEmpty());
    }
}
