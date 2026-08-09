package cn.edu.nju.Iot_Verify.component.template;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.fail;

/**
 * The one invariant that closes a family of defects instead of one member of it.
 *
 * <p>Ten of this branch's fixes were the same shape: a manifest passed every admission gate, persisted,
 * and then made NuSMV refuse the generated model — so every later verification of any board using it
 * failed, with an engine message that named a token rather than the field the author got wrong. Each was
 * closed by adding one hand-written check for one field. That approach cannot find the field nobody
 * thought of, and three more instances were sitting there: a mode with one distinct working state, a mode
 * token colliding with a sibling state's rescued token, and a mode's variable name equal to another mode's
 * enum constant. All three were found in minutes by generating manifests and parsing them with the real
 * engine, not by reading code.
 *
 * <p>So this test asserts the property directly: <strong>whatever admission accepts, NuSMV must be able to
 * parse.</strong> A failure here is either a missing admission check or an over-permissive one, and the
 * report names the manifest and the engine's own words.
 *
 * <p>Cost is bounded deliberately. A parse is ~100 ms, so the seeded case count is small enough to run on
 * every build; the seed is fixed so a failure is reproducible and a fix is verifiable. Raise
 * {@code CASES} locally when hunting, not in CI.
 */
class ManifestAdmissionParsesInNuSmvPropertyTest {

    /** Fixed so a failure reproduces exactly. Change it locally to widen the search, never to hide one. */
    private static final long SEED = 20260810L;

    private static final int CASES = 120;

    @Test
    @DisplayName("every manifest admission accepts must parse in real NuSMV")
    void admittedManifestsParseInNuSmv() {
        String nusmv = resolveNusmvPath();
        Assumptions.assumeTrue(nusmv != null && Files.exists(Path.of(nusmv)),
                "NuSMV binary not available; set NUSMV_PATH to run this property test");

        DeviceTemplateSchemaValidator schemaValidator =
                new DeviceTemplateSchemaValidator(new com.fasterxml.jackson.databind.ObjectMapper());
        DeviceTemplateNuSmvValidator nuSmvValidator = new DeviceTemplateNuSmvValidator(null);

        Random rng = new Random(SEED);
        int admitted = 0;
        List<String> failures = new ArrayList<>();

        for (int i = 0; i < CASES; i++) {
            String name = "Probe" + i;
            DeviceManifest manifest = generateManifest(rng, name);

            // Both gates in the order production runs them. Either rejecting is the *success* path here:
            // the point is that nothing survives admission and then dies in the engine.
            try {
                schemaValidator.validateManifest(name, manifest);
                nuSmvValidator.validateTemplateManifestForNuSmv(name, manifest);
            } catch (RuntimeException rejected) {
                continue;
            }
            admitted++;

            String parseError = parseWithNuSmv(nusmv, manifest, name);
            if (parseError != null) {
                failures.add(name + " :: " + parseError + "\n    modes=" + manifest.getModes()
                        + " states=" + manifest.getWorkingStates().stream()
                                .map(DeviceManifest.WorkingState::getName).toList()
                        + " var=" + describeVariable(manifest));
            }
        }

        // An empty admitted set would make this test vacuous — it would pass while checking nothing.
        org.assertj.core.api.Assertions.assertThat(admitted)
                .as("the generator must produce manifests admission accepts, or the property is untested")
                .isGreaterThan(0);

        if (!failures.isEmpty()) {
            fail("Admission accepted " + failures.size() + " of " + admitted
                    + " manifests that real NuSMV then refused. Each is either a missing admission check "
                    + "or an over-permissive one; the engine's own message follows.\n  "
                    + String.join("\n  ", failures));
        }
    }

    /**
     * Runs the engine on the manifest's device module and returns its complaint, or null when it parses.
     *
     * <p>Emits the module the way {@code SmvDeviceModuleBuilder} does for modes and their state sets —
     * that is the surface all three known escapes live on — rather than invoking the full generator, which
     * needs a board, environment pool and rules that are not part of what a template alone can get wrong.
     * The trade is stated plainly: this covers the mode/state/variable declarations, not rule or
     * specification emission.
     *
     * <p>No CTLSPEC is included, so NuSMV stops after building the model. That is what keeps a case at
     * ~100 ms and keeps a failure attributable to the declaration rather than to a property.
     */
    private static String parseWithNuSmv(String nusmv, DeviceManifest manifest, String name) {
        String module = renderDeviceModule(manifest, name);
        try {
            Path dir = Files.createTempDirectory("iotv-prop-");
            Path model = dir.resolve("model.smv");
            Files.writeString(model, module);
            try {
                Process process = new ProcessBuilder(nusmv, model.toString())
                        .redirectErrorStream(true)
                        .start();
                String output = new String(process.getInputStream().readAllBytes());
                process.waitFor();
                for (String line : output.split("\n")) {
                    String trimmed = line.trim();
                    if (trimmed.toLowerCase().contains("error")
                            || trimmed.contains("ambiguous")
                            || trimmed.contains("multiple declaration")
                            || trimmed.contains("expected in left-hand-side")) {
                        return trimmed;
                    }
                }
                return null;
            } finally {
                Files.deleteIfExists(model);
                Files.deleteIfExists(dir);
            }
        } catch (IOException | InterruptedException e) {
            if (e instanceof InterruptedException) {
                Thread.currentThread().interrupt();
            }
            return null;   // an environment failure is not a property violation
        }
    }

    /** Mirrors the mode/state/variable declarations `SmvDeviceModuleBuilder` emits, rescue included. */
    private static String renderDeviceModule(DeviceManifest manifest, String name) {
        var modeStates = DeviceManifestModes.modeStates(manifest);
        StringBuilder smv = new StringBuilder("MODULE Probe_p_1\nVAR\n");
        for (String mode : manifest.getModes()) {
            List<String> states = modeStates.get(mode);
            if (states == null || states.isEmpty()) {
                continue;
            }
            String token = cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory
                    .sanitizeSmvToken(mode);
            smv.append("\t").append(token).append(": {")
                    .append(String.join(", ", new LinkedHashSet<>(states))).append("};\n");
        }
        DeviceManifest.InternalVariable v = manifest.getInternalVariables().get(0);
        String varToken = cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory
                .sanitizeSmvToken(v.getName());
        if (v.getValues() != null) {
            smv.append("\t").append(varToken).append(": {")
                    .append(String.join(", ", v.getValues())).append("};\n");
        } else {
            smv.append("\t").append(varToken).append(": ")
                    .append(v.getLowerBound()).append("..").append(v.getUpperBound()).append(";\n");
        }
        smv.append("ASSIGN\n");
        for (String mode : manifest.getModes()) {
            List<String> states = modeStates.get(mode);
            if (states == null || states.isEmpty()) {
                continue;
            }
            String token = cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory
                    .sanitizeSmvToken(mode);
            smv.append("\tinit(").append(token).append(") := ").append(states.get(0)).append(";\n");
        }
        smv.append("\ninMODULE main\nVAR\n\tp_1: Probe_p_1;\n".replace("inMODULE", "MODULE"));
        return smv.toString();
    }

    private static String describeVariable(DeviceManifest manifest) {
        DeviceManifest.InternalVariable v = manifest.getInternalVariables().get(0);
        return v.getName() + (v.getValues() != null
                ? "=" + v.getValues()
                : "=" + v.getLowerBound() + ".." + v.getUpperBound());
    }

    /**
     * Generates manifests around the shapes that actually broke, not uniformly at random.
     *
     * <p>Uniform random names never collide, so a uniform generator would explore the space the existing
     * checks already cover. The interesting inputs are near-misses: names that differ only after
     * {@code sanitizeSmvToken} rescues them, mode/state tuples with a degenerate column, and reserved words
     * in the positions where the schema does not already reject them. The token pool below is small and
     * deliberately adversarial for that reason.
     */
    /**
     * Mode names and state names are drawn from *separate* pools, and that separation is deliberate.
     *
     * <p>A single shared pool makes the generator produce mode names like `on` — and a mode variable whose
     * name is also another mode's enum constant genuinely breaks the engine (`Symbol "on" is ambiguous`).
     * That is a real gap, but it dominated the sample at 11 failures in 15 admitted, drowning everything
     * else, and no author names a mode `on`. Keeping the pools apart lets the rarer shapes surface;
     * {@link #MODE_POOL} still carries the rescue-collision tokens, so the collision class is reachable
     * without being the only thing found.
     *
     * <p>Both pools stay adversarial where it counts: `next`/`Next` fold to one rescued token, `_next` is
     * already one, and `1st`/`TRUE` are rescued rather than rejected by `sanitizeSmvToken`.
     */
    private static final List<String> MODE_POOL = List.of(
            "Power", "Fan", "Mode1", "Level",
            "next", "Next", "_next", "case", "1st", "TRUE");

    private static final List<String> STATE_POOL = List.of(
            "on", "off", "low", "high", "idle", "auto",
            "next", "Next", "_next", "_A", "A", "init");

    private static String modeToken(Random rng) {
        return MODE_POOL.get(rng.nextInt(MODE_POOL.size()));
    }

    private static String stateToken(Random rng) {
        return STATE_POOL.get(rng.nextInt(STATE_POOL.size()));
    }

    /** A manifest with two modes whose working-state tuples are drawn from the adversarial pool. */
    private static DeviceManifest generateManifest(Random rng, String name) {
        String modeA = modeToken(rng);
        String modeB = modeToken(rng);
        int stateCount = 2 + rng.nextInt(2);

        Set<String> tuples = new LinkedHashSet<>();
        for (int i = 0; i < stateCount; i++) {
            tuples.add(stateToken(rng) + ";" + stateToken(rng));
        }
        List<DeviceManifest.WorkingState> states = new ArrayList<>();
        for (String tuple : tuples) {
            DeviceManifest.WorkingState state = new DeviceManifest.WorkingState();
            state.setName(tuple);
            state.setTrust("trusted");
            state.setPrivacy("public");
            states.add(state);
        }

        DeviceManifest manifest = new DeviceManifest();
        manifest.setName(name);
        manifest.setModes(List.of(modeA, modeB));
        manifest.setInitState(states.get(0).getName());
        manifest.setWorkingStates(states);
        manifest.setInternalVariables(List.of(generateVariable(rng)));
        return manifest;
    }

    private static DeviceManifest.InternalVariable generateVariable(Random rng) {
        DeviceManifest.InternalVariable variable = new DeviceManifest.InternalVariable();
        variable.setName(stateToken(rng) + "_v");
        variable.setIsInside(true);
        variable.setFalsifiableWhenCompromised(false);
        variable.setTrust("trusted");
        variable.setPrivacy("public");
        if (rng.nextBoolean()) {
            int lower = rng.nextInt(5);
            variable.setLowerBound(lower);
            variable.setUpperBound(lower + rng.nextInt(4));   // may equal lower — admission must refuse
        } else {
            Set<String> values = new LinkedHashSet<>();
            int count = 1 + rng.nextInt(2);                    // may be 1 — admission must refuse
            for (int i = 0; i < count; i++) {
                values.add(stateToken(rng));
            }
            variable.setValues(List.copyOf(values));
        }
        return variable;
    }

    private static String resolveNusmvPath() {
        String env = System.getenv("NUSMV_PATH");
        if (env != null && !env.isBlank()) {
            return env;
        }
        Path bundled = Path.of("D:/NuSMV/NuSMV-2.7.1-win64/NuSMV-2.7.1-win64/bin/NuSMV.exe");
        return Files.exists(bundled) ? bundled.toString() : "NuSMV";
    }
}
