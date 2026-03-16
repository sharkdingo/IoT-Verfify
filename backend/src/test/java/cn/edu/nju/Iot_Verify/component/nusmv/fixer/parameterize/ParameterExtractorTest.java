package cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class ParameterExtractorTest {

    @Test
    void extract_findsValuesInState() {
        String output = """
                -- specification EF !(a_temperature>param_r0_c0)  is false
                -- as demonstrated by the following execution sequence
                Trace Description: CTL Counterexample
                Trace Type: Counterexample
                  -> State: 1.1 <-
                    param_r0_c0 = 25
                    lambda_r0_c1 = TRUE
                    a_temperature = 30
                  -> State: 1.2 <-
                    a_temperature = 28
                """;

        Map<String, String> result = ParameterExtractor.extract(output,
                List.of("param_r0_c0", "lambda_r0_c1"));

        assertEquals(2, result.size());
        assertEquals("25", result.get("param_r0_c0"));
        assertEquals("TRUE", result.get("lambda_r0_c1"));
    }

    @Test
    void extract_onlyRequestedVars() {
        String output = """
                  -> State: 1.1 <-
                    param_r0_c0 = 25
                    lambda_r0_c1 = TRUE
                    a_temperature = 30
                """;

        Map<String, String> result = ParameterExtractor.extract(output,
                List.of("param_r0_c0"));

        assertEquals(1, result.size());
        assertEquals("25", result.get("param_r0_c0"));
        assertNull(result.get("lambda_r0_c1"));
    }

    @Test
    void extract_nullOutput_returnsEmpty() {
        assertTrue(ParameterExtractor.extract(null, List.of("x")).isEmpty());
    }

    @Test
    void extract_blankOutput_returnsEmpty() {
        assertTrue(ParameterExtractor.extract("", List.of("x")).isEmpty());
    }

    @Test
    void extract_nullVarNames_returnsEmpty() {
        assertTrue(ParameterExtractor.extract("-> State: 1.1 <-\n  x = 1", null).isEmpty());
    }

    @Test
    void extract_emptyVarNames_returnsEmpty() {
        assertTrue(ParameterExtractor.extract("-> State: 1.1 <-\n  x = 1", List.of()).isEmpty());
    }

    @Test
    void extract_noStateSection_returnsEmpty() {
        String output = "NuSMV > -- no counterexample --\n";
        assertTrue(ParameterExtractor.extract(output, List.of("param_r0_c0")).isEmpty());
    }

    @Test
    void extract_stopsAtNextSection() {
        String output = """
                  -> State: 1.1 <-
                    param_r0_c0 = 25
                  -> State: 1.2 <-
                    param_r0_c0 = 99
                """;

        // Only first state should be scanned
        Map<String, String> result = ParameterExtractor.extract(output,
                List.of("param_r0_c0"));

        assertEquals("25", result.get("param_r0_c0"));
    }

    @Test
    void extract_booleanValues() {
        String output = """
                  -> State: 1.1 <-
                    lambda_r0_c0 = FALSE
                    lambda_r0_c1 = TRUE
                """;

        Map<String, String> result = ParameterExtractor.extract(output,
                List.of("lambda_r0_c0", "lambda_r0_c1"));

        assertEquals("FALSE", result.get("lambda_r0_c0"));
        assertEquals("TRUE", result.get("lambda_r0_c1"));
    }
}
