package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.io.TempDir;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.TimeUnit;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.junit.jupiter.api.Assertions.fail;

/**
 * Real NuSMV smoke coverage for the witness-extraction assumption used by
 * ParameterAdjustStrategy. The strategy relies on a false negated CTL spec
 * producing a counterexample that includes FROZENVAR assignments.
 */
class ParameterAdjustStrategyNusmvWitnessIntegrationTest {

    private static final String REQUIRED_NUSMV_VERSION = "NuSMV 2.7.1";

    @TempDir
    Path tempDir;

    @Test
    void falseEfAndEgCounterexamplesExposeFrozenVarAssignments() throws Exception {
        String nusmv = findNusmvExecutable();
        requireNusmvInCi(nusmv);
        Assumptions.assumeTrue(nusmv != null, "NuSMV executable not found");

        assertFalseSpecExposesLambda(nusmv, "EF(lambda = 1)", "ef_false.smv");
        assertFalseSpecExposesLambda(nusmv, "EG(lambda = 1)", "eg_false.smv");
        assertFalseSpecExposesLambda(nusmv, "EF((lambda = 1) & EG(!s))", "ef_nested_eg_false.smv");
    }

    private void requireNusmvInCi(String nusmv) {
        if (nusmv != null) {
            return;
        }
        if (isCi()) {
            fail("NuSMV executable not found. CI must install NuSMV 2.7.1 and expose it via NUSMV_PATH or PATH.");
        }
    }

    private void assertFalseSpecExposesLambda(String nusmv, String ctlSpec, String fileName) throws Exception {
        Path model = tempDir.resolve(fileName);
        Files.writeString(model, """
                MODULE main
                FROZENVAR
                  lambda : 0..1;
                VAR
                  s : boolean;
                ASSIGN
                  init(s) := FALSE;
                  next(s) := s;
                CTLSPEC %s
                """.formatted(ctlSpec), StandardCharsets.US_ASCII);

        Process process = new ProcessBuilder(nusmv, model.toString())
                .redirectErrorStream(true)
                .start();
        boolean finished = process.waitFor(Duration.ofSeconds(10).toMillis(), TimeUnit.MILLISECONDS);
        if (!finished) {
            process.destroyForcibly();
        }
        assertTrue(finished, "NuSMV did not finish within timeout");

        String output = new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8);
        assertEquals(0, process.exitValue(), output);
        requireNusmvVersionFromModelRun(output);
        assertTrue(output.toLowerCase().contains("is false"), output);
        assertTrue(output.matches("(?s).*lambda\\s*=\\s*0.*"), output);
    }

    private void requireNusmvVersionFromModelRun(String output) {
        if (output.contains(REQUIRED_NUSMV_VERSION)) {
            return;
        }
        String firstLine = output.lines().findFirst().orElse(output);
        if (isCi()) {
            fail("Expected " + REQUIRED_NUSMV_VERSION + " in CI, but NuSMV reported:\n" + firstLine);
        }
        Assumptions.assumeTrue(false,
                "NuSMV 2.7.1 required for this smoke test, but found: " + firstLine);
    }

    private String findNusmvExecutable() throws IOException, InterruptedException {
        String fromEnv = System.getenv("NUSMV_PATH");
        if (fromEnv != null && !fromEnv.isBlank() && Files.exists(Path.of(fromEnv))) {
            return fromEnv;
        }

        List<String> command = new ArrayList<>();
        if (System.getProperty("os.name", "").toLowerCase().contains("win")) {
            command.add("where.exe");
        } else {
            command.add("which");
        }
        command.add("NuSMV");

        Process process = new ProcessBuilder(command)
                .redirectErrorStream(true)
                .start();
        boolean finished = process.waitFor(5, TimeUnit.SECONDS);
        if (!finished || process.exitValue() != 0) {
            return null;
        }
        String output = new String(process.getInputStream().readAllBytes(), StandardCharsets.UTF_8).trim();
        if (output.isBlank()) {
            return null;
        }
        return output.lines().findFirst().orElse(null);
    }

    private boolean isCi() {
        return "true".equalsIgnoreCase(System.getenv("CI"))
                || "true".equalsIgnoreCase(System.getenv("GITHUB_ACTIONS"));
    }
}
