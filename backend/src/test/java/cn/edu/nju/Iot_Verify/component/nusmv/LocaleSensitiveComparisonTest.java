package cn.edu.nju.Iot_Verify.component.nusmv;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Case-folding that decides a keyword must pin {@code Locale.ROOT}.
 *
 * <p>{@code SmvSpecificationBuilder.normalizeSpecTargetType} documents the reason: a Turkish default locale maps
 * {@code I} to the dotless {@code ı}, so {@code "API".toLowerCase()} becomes {@code "apı"} and matches no keyword.
 * That comment was the only thing enforcing the rule, and three places had already drifted from it:
 *
 * <ul>
 *   <li>{@code NusmvRequestValidator} lowercased {@code targetType} twice without a locale — under a Turkish
 *       locale a valid {@code API} condition would have been rejected as an invalid target type.</li>
 *   <li>{@code DeviceSmvDataFactory} compared three identifiers against {@code NUSMV_RESERVED_WORDS} without one,
 *       which is worse: {@code INIT} folds to {@code ınıt}, misses the reserved-word set, and is emitted verbatim
 *       into the model — so a reserved word reaches NuSMV as a variable name instead of being rescued.</li>
 *   <li>{@code FixStrategyApplier} normalized a condition's {@code targetType} the same way.</li>
 * </ul>
 *
 * <p>There is no test here asserting that a Turkish locale folds {@code I} to {@code ı}: that is JDK behaviour
 * over literals a test would write itself, so no repo change could redden it. The premise is proven where it
 * matters instead - {@code ProductionSafetyCheckTest.isProductionProfile_holdsUnderATurkishDefaultLocale} swaps
 * the JVM default locale for real and fails if the pin is removed.
 *
 * <p>The exemptions below are deliberate and narrow: folding for a substring search in log text or an OS name is
 * not deciding a keyword, and its input is not user data that has to round-trip.
 */
class LocaleSensitiveComparisonTest {

    /** Directories whose case-folding participates in model generation or request validation. */
    private static final List<String> SCANNED = List.of("src/main/java");

    /**
     * Lines where a bare fold is correct.
     *
     * <p>Each is a substring search over text the product does not have to interpret exactly: the JVM's own
     * {@code os.name}, and NuSMV's English stdout scanned for a marker word. Neither can be affected by a
     * Turkish {@code I}, and neither result is compared against a keyword the user supplied.
     */
    private static final List<String> ALLOWED_SUBSTRING_SEARCHES = List.of(
            "System.getProperty(\"os.name\")",
            "logLine.toLowerCase()",
            "logLine != null && logLine.toLowerCase()",
            // English diagnostic prose interpolated into a BadRequestException message, not a keyword decision.
            // A dotless i would read oddly in one sentence; it cannot change a comparison or a wire value.
            "requestKind.toLowerCase()");

    @Test
    @DisplayName("no bare toLowerCase/toUpperCase decides a NuSMV keyword or request vocabulary")
    void caseFoldingThatDecidesAKeywordPinsTheRootLocale() throws IOException {
        List<String> offenders = new ArrayList<>();
        for (String dir : SCANNED) {
            Path root = Paths.get(dir);
            // Assert rather than skip: a renamed package would otherwise leave the scan silently, which is the
            // failure mode this class's own doc warns about.
            assertTrue(Files.isDirectory(root), "scan root should exist: " + dir);
            try (Stream<Path> stream = Files.walk(root)) {
                for (Path file : stream.filter(path -> path.toString().endsWith(".java")).toList()) {
                    String[] lines = Files.readString(file, StandardCharsets.UTF_8).split("\r?\n");
                    for (int i = 0; i < lines.length; i++) {
                        String line = lines[i];
                        if (line.stripLeading().startsWith("*") || line.stripLeading().startsWith("//")) continue;
                        if (!line.contains(".toLowerCase()") && !line.contains(".toUpperCase()")) continue;
                        if (ALLOWED_SUBSTRING_SEARCHES.stream().anyMatch(line::contains)) continue;
                        offenders.add(file.getFileName() + ":" + (i + 1) + "  " + line.trim());
                    }
                }
            }
        }

        assertTrue(offenders.isEmpty(),
                "pin Locale.ROOT, or add the line to ALLOWED_SUBSTRING_SEARCHES with a reason:\n"
                        + String.join("\n", offenders));
    }

}
