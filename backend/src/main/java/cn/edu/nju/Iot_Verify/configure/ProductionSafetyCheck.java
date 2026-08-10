package cn.edu.nju.Iot_Verify.configure;

import cn.edu.nju.Iot_Verify.component.template.DeviceTemplateNuSmvValidator;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto;
import com.fasterxml.jackson.databind.DeserializationFeature;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.datatype.jsr310.JavaTimeModule;
import jakarta.annotation.PostConstruct;
import lombok.extern.slf4j.Slf4j;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.core.env.Environment;
import org.springframework.core.io.Resource;
import org.springframework.core.io.support.PathMatchingResourcePatternResolver;
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
    private final DeviceTemplateNuSmvValidator templateValidator;

    @Value("${jwt.secret:}")
    private String jwtSecret;

    @Value("${spring.datasource.password:}")
    private String dbPassword;

    @Value("${llm.api-key:}")
    private String llmApiKey;

    public ProductionSafetyCheck(Environment environment, DeviceTemplateNuSmvValidator templateValidator) {
        this.environment = environment;
        this.templateValidator = templateValidator;
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

        // Validate bundled default templates (added in round 11 audit)
        // Only run if templateValidator is available (not in unit tests with null)
        if (templateValidator != null) {
            violations.addAll(validateBundledDefaultTemplates());
        }

        if (!violations.isEmpty()) {
            String msg = "Production safety check failed - insecure defaults detected:\n  - "
                    + String.join("\n  - ", violations);
            throw new IllegalStateException(msg);
        }

        log.info("Production safety check passed");
    }

    /**
     * Validates all bundled default templates in classpath:/deviceTemplate/*.json.
     * <p>
     * A malformed or collision-vulnerable default template would break every user's first board access
     * with a 500 error. This check catches it at startup instead of in production.
     * <p>
     * Added in adversarial audit round 11, which found that a bundled template with variable name
     * collisions (a_ prefix, reserved words, mode-variable conflicts) would not be detected until
     * runtime user access.
     *
     * @return list of validation error messages, empty if all templates are valid
     */
    private List<String> validateBundledDefaultTemplates() {
        List<String> errors = new ArrayList<>();
        PathMatchingResourcePatternResolver resolver = new PathMatchingResourcePatternResolver();

        // Create ObjectMapper with same config as the app uses for bundled templates
        ObjectMapper mapper = new ObjectMapper();
        mapper.registerModule(new JavaTimeModule());
        mapper.configure(DeserializationFeature.FAIL_ON_UNKNOWN_PROPERTIES, false);
        mapper.configure(com.fasterxml.jackson.databind.MapperFeature.ACCEPT_CASE_INSENSITIVE_PROPERTIES, true);

        try {
            Resource[] resources = resolver.getResources("classpath:deviceTemplate/*.json");
            log.info("Validating {} bundled default templates", resources.length);

            for (Resource resource : resources) {
                try {
                    String json = new String(resource.getInputStream().readAllBytes());
                    DeviceTemplateDto template = mapper.readValue(json, DeviceTemplateDto.class);

                    if (template == null || template.getManifest() == null) {
                        errors.add("Bundled template " + resource.getFilename() + " has null manifest");
                        continue;
                    }

                    // Run the same admission gates that user uploads go through
                    templateValidator.validateTemplateManifestForNuSmv(template.getName(), template.getManifest());

                } catch (Exception e) {
                    errors.add("Bundled template " + resource.getFilename() + " validation failed: " + e.getMessage());
                }
            }

            if (errors.isEmpty()) {
                log.info("All {} bundled default templates passed validation", resources.length);
            }

        } catch (Exception e) {
            errors.add("Failed to load bundled templates: " + e.getMessage());
        }

        return errors;
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
