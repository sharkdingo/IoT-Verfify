package cn.edu.nju.Iot_Verify.component.aitool;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An AI tool must reach the database through the service layer, never a repository.
 *
 * <p>This is what makes an assistant-made board change as safe as a hand-made one, and it is entirely structural.
 * The services own the per-user write lock, the ownership check, and — critically — the
 * {@code BoardEditJournal.record} call that happens inside the mutation's own transaction. A tool that injected a
 * repository directly would bypass all three: the change would commit, it would be invisible to the journal, and
 * {@code /api/board/edits/availability} would correctly report that there is nothing to undo. The user's rule
 * would simply be gone, permanently, with no error anywhere.
 *
 * <p>{@code BoardStorageController} states the reason this cannot be patched client-side: "the journal on the
 * server is the authority for what is reversible, so the client sends no local history." There is no second place
 * to catch the omission.
 *
 * <p>Verified live before writing this: a rule created through the service path reported {@code canUndo=true},
 * undo removed it, redo restored it; a device rename was journalled and undo restored the *exact* previous label;
 * and a rename carrying a stale {@code expectedLabel} was refused with 409 while the newer human edit survived.
 * The layering is currently clean — 53 tools reference a service, zero reference a repository.
 *
 * <p>Source-level on purpose. The failure is an import plus a constructor parameter, which compiles, passes a
 * happy-path Mockito test, and works perfectly in manual testing. Nothing else in the suite would notice.
 */
class AiToolLayeringContractTest {

    private static final Path TOOL_ROOT =
            Paths.get("src", "main", "java", "cn", "edu", "nju", "Iot_Verify", "component", "aitool");

    /** A field or constructor parameter whose type is a repository. */
    private static final Pattern REPOSITORY_DEPENDENCY = Pattern.compile(
            "(?:private\\s+final\\s+|,\\s*|\\(\\s*)([A-Z][A-Za-z0-9]*Repository)\\s+[a-z][A-Za-z0-9]*");

    private static List<Path> toolSources() throws IOException {
        try (Stream<Path> paths = Files.walk(TOOL_ROOT)) {
            return paths.filter(Files::isRegularFile)
                    .filter(p -> p.getFileName().toString().endsWith("Tool.java"))
                    .toList();
        }
    }

    @Test
    @DisplayName("no AI tool injects a repository, so every AI mutation inherits journalling and ownership")
    void aiToolsGoThroughServices() throws IOException {
        List<Path> sources = toolSources();

        // Coverage first. If the directory moved, an empty offender list would be vacuously true and this test
        // would pass while reading nothing — the failure mode this audit has hit repeatedly.
        assertTrue(sources.size() >= 50,
                "expected at least 50 AI tool sources under " + TOOL_ROOT + ", found " + sources.size()
                        + " — the tool package probably moved, so an empty offender list proves nothing");

        List<String> offenders = new ArrayList<>();
        for (Path source : sources) {
            String text = Files.readString(source, StandardCharsets.UTF_8);
            // Strip comments so a javadoc line naming a repository is not mistaken for a dependency on one.
            String code = text.replaceAll("(?s)/\\*.*?\\*/", "").replaceAll("(?m)//.*$", "");
            Matcher matcher = REPOSITORY_DEPENDENCY.matcher(code);
            while (matcher.find()) {
                offenders.add(source.getFileName() + " injects " + matcher.group(1));
            }
        }

        assertEquals(List.of(), offenders,
                "an AI tool reaching a repository directly bypasses the per-user write lock, the ownership check, "
                        + "and BoardEditJournal.record — the mutation would commit but could never be undone");
    }

    @Test
    @DisplayName("AI tools do depend on services, so the rule is not satisfied by tools that touch nothing")
    void aiToolsActuallyUseServices() throws IOException {
        // The mirror assertion. Without it, deleting every dependency from every tool would satisfy the rule above
        // and destroy the assistant — a rule that can be satisfied by removing the feature is not a rule.
        Pattern serviceDependency = Pattern.compile(
                "(?:private\\s+final\\s+|,\\s*|\\(\\s*)([A-Z][A-Za-z0-9]*Service)\\s+[a-z][A-Za-z0-9]*");

        int withService = 0;
        for (Path source : toolSources()) {
            String code = Files.readString(source, StandardCharsets.UTF_8)
                    .replaceAll("(?s)/\\*.*?\\*/", "").replaceAll("(?m)//.*$", "");
            if (serviceDependency.matcher(code).find()) withService++;
        }

        assertTrue(withService >= 40,
                "expected most AI tools to depend on a service; only " + withService + " do, which suggests the "
                        + "layering moved somewhere this test can no longer see");
    }
}
