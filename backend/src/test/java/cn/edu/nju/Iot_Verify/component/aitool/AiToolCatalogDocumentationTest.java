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

    /**
     * A tool's schema is what the model plans against; {@code requireOnlyFields} is what the tool
     * accepts. A field advertised by one and refused by the other costs the model a round on a
     * guaranteed {@code VALIDATION_ERROR}, and the model cannot see the allowlist to know better.
     *
     * <p>The catalog is consistent today, so this test does not fix anything — it removes the need to
     * remember. The rule was previously carried only as prose in {@code backend/CLAUDE.md}, and the
     * two declaration idioms in use ({@code props.put(...)} and an inline {@code Map.of(...)} passed
     * straight to the constructor) make the drift easy to introduce and invisible in review.
     *
     * <p>Checked in one direction only. A name the allowlist accepts but the top-level schema omits is
     * legitimate: nested object and array members are validated by the same helper deeper in the
     * payload, so requiring symmetry would report every composite-argument tool.
     */
    @Test
    void everyAdvertisedArgumentIsAcceptedByTheToolThatAdvertisesIt() throws IOException {
        Pattern propsPut = Pattern.compile("(?:props|properties)\\.put\\(\\s*\"([^\"]+)\"");
        Pattern inlineSchema = Pattern.compile("new FunctionParameterSchema\\(\\s*\"object\"\\s*,\\s*Map\\.of\\(",
                Pattern.DOTALL);
        Pattern allowlist = Pattern.compile("requireOnlyFields\\([^;]*?Set\\.of\\(([^)]*)\\)", Pattern.DOTALL);
        Pattern quoted = Pattern.compile("\"([^\"]+)\"");

        List<String> drift = new ArrayList<>();
        int parsed = 0;

        for (Path tool : concreteTools()) {
            String source = Files.readString(tool);
            String name = tool.getFileName().toString().replace(".java", "");

            int definitionStart = source.indexOf("public LlmToolSpec getDefinition");
            if (definitionStart < 0) continue;
            int definitionEnd = source.indexOf("protected String doExecute", definitionStart);
            String definition = source.substring(definitionStart,
                    definitionEnd > 0 ? definitionEnd : source.length());

            List<String> advertised = new ArrayList<>();
            Matcher put = propsPut.matcher(definition);
            while (put.find()) advertised.add(put.group(1));
            Matcher inline = inlineSchema.matcher(definition);
            if (inline.find()) {
                advertised.addAll(topLevelKeys(definition.substring(inline.end())));
            }
            if (advertised.isEmpty()) continue;

            List<String> accepted = new ArrayList<>();
            Matcher allow = allowlist.matcher(source);
            boolean validates = false;
            while (allow.find()) {
                validates = true;
                Matcher field = quoted.matcher(allow.group(1));
                while (field.find()) accepted.add(field.group(1));
            }
            if (!validates) {
                drift.add(name + " declares " + advertised + " but never calls requireOnlyFields");
                continue;
            }
            parsed++;

            for (String field : advertised) {
                if (!accepted.contains(field)) {
                    drift.add(name + " advertises \"" + field + "\" but requireOnlyFields rejects it");
                }
            }
        }

        // A scan that matches nothing asserts nothing: if the declaration idiom changes and the parse
        // stops finding arguments, fail here rather than reporting a clean catalog.
        int toolsWithArguments = parsed;
        assertTrue(toolsWithArguments >= 40,
                () -> "expected most tools to declare arguments, parsed only " + toolsWithArguments
                        + " — the schema declaration idiom probably changed");
        assertTrue(drift.isEmpty(),
                () -> "a tool's schema and its requireOnlyFields allowlist disagree:\n"
                        + String.join("\n", drift));
    }

    /**
     * Property names of an inline {@code Map.of(...)} schema, i.e. the keys at depth 0. The nested
     * {@code Map.of("type", ..., "description", ...)} values sit deeper and are JSON-Schema keywords,
     * not argument names, so this counts parentheses instead of matching every quoted string.
     */
    private static List<String> topLevelKeys(String afterMapOf) {
        List<String> keys = new ArrayList<>();
        int depth = 0;
        boolean expectKey = true;
        for (int i = 0; i < afterMapOf.length(); i++) {
            char c = afterMapOf.charAt(i);
            if (c == '(') {
                depth++;
            } else if (c == ')') {
                if (depth == 0) break;
                depth--;
            } else if (c == ',' && depth == 0) {
                expectKey = true;
            } else if (c == '"') {
                int end = afterMapOf.indexOf('"', i + 1);
                if (end < 0) break;
                if (depth == 0 && expectKey) keys.add(afterMapOf.substring(i + 1, end));
                if (depth == 0) expectKey = false;
                i = end;
            }
        }
        return keys;
    }
}
