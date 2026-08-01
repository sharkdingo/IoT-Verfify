package cn.edu.nju.Iot_Verify.component.template;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code EnvironmentDomains} was deleted, not deprecated: read capability is now an explicit
 * {@code Reads} flag on a single {@code InternalVariables} entry.
 *
 * <p>Deleting a manifest field leaves two kinds of residue that a passing suite hides. Dead reads
 * ({@code manifestNode.path("EnvironmentDomains")}) silently return a missing node forever, so the
 * validation they feed quietly does nothing. Stale messages are worse: four told a template author to
 * "Add EnvironmentDomains[].Name=..." to fix a rejection, which the JSON schema now rejects in turn —
 * a dead end that reads as a product bug and cannot be discovered from the message itself.
 *
 * <p>This test fails on either. It is deliberately a source scan rather than a behavioural assertion:
 * the point is that no <em>future</em> path may reference the removed field, and a per-message test
 * only covers messages someone remembered to write one for.
 */
class RemovedManifestFieldResidueTest {

    private static final Path MAIN_SOURCES = Path.of("src/main/java/cn/edu/nju/Iot_Verify");

    /** The one legitimate mention: explaining in a comment what the field used to encode. */
    private static boolean isExplanatoryProse(String line) {
        String trimmed = line.trim();
        return trimmed.startsWith("//") || trimmed.startsWith("*") || trimmed.startsWith("/*");
    }

    /**
     * Only the two forms that actually reach the removed manifest field: a JSON node lookup by that
     * key, and a user-facing message naming it. Internal identifiers that merely contain the words
     * ({@code ownEnvironmentDomains}, {@code registerEnvironmentDomains}) are ordinary local naming
     * for shared-value domains and are not residue — matching those would make this test noise.
     */
    private static boolean referencesTheRemovedField(String line) {
        return line.contains("\"EnvironmentDomains\"") || line.contains("EnvironmentDomains[]");
    }

    @Test
    void noProductionCodeReferencesTheRemovedEnvironmentDomainsField() throws IOException {
        List<String> offenders = new ArrayList<>();
        try (Stream<Path> paths = Files.walk(MAIN_SOURCES)) {
            for (Path path : paths.filter(p -> p.toString().endsWith(".java")).toList()) {
                List<String> lines = Files.readAllLines(path, StandardCharsets.UTF_8);
                for (int i = 0; i < lines.size(); i++) {
                    String line = lines.get(i);
                    if (referencesTheRemovedField(line) && !isExplanatoryProse(line)) {
                        offenders.add(path + ":" + (i + 1) + " -> " + line.trim());
                    }
                }
            }
        }

        assertTrue(offenders.isEmpty(),
                "EnvironmentDomains was removed from the manifest. These lines either read a node that is "
                        + "always missing, or tell a template author to add a field the schema rejects. Point "
                        + "them at an InternalVariables entry with IsInside=false and an explicit Reads:\n"
                        + String.join("\n", offenders));
    }

    @Test
    void theJsonSchemaDoesNotDeclareTheRemovedField() throws IOException {
        String schema = Files.readString(Path.of("device-template-schema.json"), StandardCharsets.UTF_8);
        // The schema is the artifact shipped to template authors, so a lingering property definition
        // there would advertise a field every validator now refuses. The one permitted occurrence is
        // the $comment explaining why read capability must be stated rather than implied.
        int declarations = schema.split("\"EnvironmentDomains\"\\s*:", -1).length - 1;
        assertTrue(declarations == 0,
                "device-template-schema.json still declares EnvironmentDomains as a property");
    }
}
