package cn.edu.nju.Iot_Verify.configure;

import jakarta.annotation.PostConstruct;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.core.env.Environment;
import org.springframework.stereotype.Component;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Set;
import java.util.Locale;

/**
 * Fail-fast guard for production profiles.
 * When spring.profiles.active contains "prod" or "production",
 * the application refuses to start if any security-sensitive configuration
 * still uses its insecure default value.
 */
@Slf4j
@Component
public class ProductionSafetyCheck {

    /**
     * Which Spring profiles count as production, for every security decision in the product.
     *
     * <p>Private again: the shared thing is {@link #isProductionProfile(Environment)}, not this list. Exposing
     * only the set left {@code JwtUtil} with its own copy of the case fold and the loop, and the fold was the
     * part that had actually drifted — so sharing the vocabulary alone would have fixed the symptom and kept
     * the mechanism duplicated.
     */
    private static final Set<String> PRODUCTION_PROFILES = Set.of("prod", "production");
    private static final String INSECURE_JWT_SECRET_PREFIX = "iot-verify-secret-key";
    private static final String INSECURE_DB_PASSWORD = "sharkdingo123";
    private static final String PLACEHOLDER_LLM_API_KEY = "your_api_key_here";

    private final Environment environment;

    @Value("${jwt.secret:}")
    private String jwtSecret;

    @Value("${spring.datasource.password:}")
    private String dbPassword;

    @Value("${llm.api-key:}")
    private String llmApiKey;

    public ProductionSafetyCheck(Environment environment) {
        this.environment = environment;
    }

    @PostConstruct
    public void check() {
        if (!isProductionProfile(environment)) {
            return;
        }

        List<String> violations = new ArrayList<>();

        if (jwtSecret == null || jwtSecret.isBlank() || jwtSecret.startsWith(INSECURE_JWT_SECRET_PREFIX)) {
            violations.add("jwt.secret (JWT_SECRET) is still the insecure default or empty");
        }

        if (INSECURE_DB_PASSWORD.equals(dbPassword)) {
            violations.add("spring.datasource.password (DB_PASSWORD) is still the insecure default");
        }

        if (llmApiKey == null || llmApiKey.isBlank() || PLACEHOLDER_LLM_API_KEY.equals(llmApiKey)) {
            violations.add("llm.api-key (IOT_VERIFY_OPENAI_API_KEY) is still the placeholder default or empty");
        }

        if (!violations.isEmpty()) {
            String msg = "Production safety check failed - insecure defaults detected:\n  - "
                    + String.join("\n  - ", violations);
            throw new IllegalStateException(msg);
        }

        log.info("Production safety check passed");
    }

    /**
     * Whether the running application is in production, for every security decision in the product.
     *
     * <p>This owns the whole decision — the profile vocabulary, the case fold, and the loop — because
     * {@code JwtUtil} needs the same answer for its insecure-JWT-secret warning and previously duplicated all
     * three. Sharing only the {@code Set} still left two copies of the fold, and the fold is exactly what had
     * gone wrong: with the JVM's default locale a Turkish server folds {@code PRODUCTION} to {@code productıon}
     * (dotless ı), which matches neither profile name, so this guard would not fire and the application would
     * boot with default {@code JWT_SECRET}, {@code DB_PASSWORD} and {@code IOT_VERIFY_OPENAI_API_KEY}.
     * {@code Locale.ROOT} is therefore load-bearing, not incidental — see the documented rule on
     * {@code SmvSpecificationBuilder.normalizeSpecTargetType}.
     */
    public static boolean isProductionProfile(Environment environment) {
        if (environment == null) {
            return false;
        }
        return Arrays.stream(environment.getActiveProfiles())
                .anyMatch(p -> p != null && PRODUCTION_PROFILES.contains(p.toLowerCase(Locale.ROOT)));
    }
}
