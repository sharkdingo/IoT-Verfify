package cn.edu.nju.Iot_Verify.component.aitool;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Makes the AI tool catalog size authoritative in code instead of hand-maintained in prose.
 *
 * <p>The tool count appears in six user-facing documents. Nothing connected them to the code, so the
 * only thing preventing drift was remembering to update all six — and a count that is wrong is worse
 * than no count, because a reader cannot tell which number to trust.
 *
 * <p>A full Spring context would be the most direct source of truth, but it is heavy for one integer
 * and the registry is discovered by classpath scanning anyway. Counting the concrete implementations
 * on disk is equivalent, needs no context, and fails fast with the exact files and documents involved.
 */
class AiToolCatalogDocumentationTest {

    private static final Path TOOL_ROOT =
            Path.of("src/main/java/cn/edu/nju/Iot_Verify/component/aitool");

    /** Documents that state the catalog size, and the repo-relative path to each. */
    private static final List<String> DOCUMENTS = List.of(
            "../README.md",
            "../docs/README.md",
            "../docs/api/ai-tools.md",
            "../docs/architecture/overview.md",
            "CLAUDE.md",
            "README.md");

    private static List<Path> concreteTools() throws IOException {
        try (Stream<Path> paths = Files.walk(TOOL_ROOT)) {
            List<Path> tools = new ArrayList<>();
            for (Path path : paths.filter(p -> p.toString().endsWith(".java")).toList()) {
                String source = Files.readString(path);
                // A registered tool is a concrete Spring bean implementing AiTool. AbstractAiTool
                // itself implements the interface but is abstract, so it is not a catalog entry.
                boolean isTool = source.contains("extends AbstractAiTool")
                        || source.matches("(?s).*\\bimplements\\s+AiTool\\b.*");
                if (isTool && !source.contains("abstract class")) {
                    tools.add(path);
                }
            }
            return tools;
        }
    }

    @Test
    void everyDocumentReportsTheActualNumberOfRegisteredTools() throws IOException {
        List<Path> tools = concreteTools();
        int actual = tools.size();
        assertTrue(actual > 0, "no AI tools found; the discovery rule itself is broken");

        Pattern claim = Pattern.compile("(?<!\\d)(\\d{2,3})\\s+(?:built-in\\s+|AI\\s+)?tools\\b");
        Map<String, List<String>> wrong = new LinkedHashMap<>();
        int documentsChecked = 0;

        for (String document : DOCUMENTS) {
            Path path = Path.of(document);
            if (!Files.exists(path)) continue;
            documentsChecked++;
            Matcher matcher = claim.matcher(Files.readString(path));
            List<String> claimed = new ArrayList<>();
            while (matcher.find()) {
                claimed.add(matcher.group(1));
            }
            for (String value : claimed) {
                if (Integer.parseInt(value) != actual) {
                    wrong.computeIfAbsent(document, key -> new ArrayList<>()).add(value);
                }
            }
        }

        assertEquals(DOCUMENTS.size(), documentsChecked,
                "a document that states the tool count moved or was renamed; update DOCUMENTS");
        assertTrue(wrong.isEmpty(),
                () -> "the catalog has " + actual + " tools but these documents disagree: " + wrong
                        + ". Update them, or update this list if a tool was added or removed.");
    }

    @Test
    void toolDiscoveryExcludesTheAbstractBaseClass() throws IOException {
        List<String> names = concreteTools().stream()
                .map(path -> path.getFileName().toString())
                .toList();

        assertFalse(names.contains("AbstractAiTool.java"),
                "AbstractAiTool implements AiTool but is abstract; counting it inflates the catalog");
        assertTrue(names.stream().allMatch(name -> name.endsWith("Tool.java")),
                () -> "every catalog entry should be a *Tool class, got: " + names);
    }
}
