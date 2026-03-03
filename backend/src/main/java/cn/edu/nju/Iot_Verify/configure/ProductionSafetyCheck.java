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

/**
 * Fail-fast guard for production profiles.
 * When spring.profiles.active contains "prod" or "production",
 * the application refuses to start if any security-sensitive configuration
 * still uses its insecure default value.
 */
@Slf4j
@Component
public class ProductionSafetyCheck {

    private static final Set<String> PRODUCTION_PROFILES = Set.of("prod", "production");
    private static final String INSECURE_JWT_SECRET_PREFIX = "iot-verify-secret-key";
    private static final String INSECURE_DB_PASSWORD = "sharkdingo123";
    private static final String PLACEHOLDER_ARK_API_KEY = "your_api_key_here";

    private final Environment environment;

    @Value("${jwt.secret:}")
    private String jwtSecret;

    @Value("${spring.datasource.password:}")
    private String dbPassword;

    @Value("${volcengine.ark.api-key:}")
    private String arkApiKey;

    public ProductionSafetyCheck(Environment environment) {
        this.environment = environment;
    }

    @PostConstruct
    public void check() {
        if (!isProductionProfile()) {
            return;
        }

        List<String> violations = new ArrayList<>();

        if (jwtSecret != null && jwtSecret.startsWith(INSECURE_JWT_SECRET_PREFIX)) {
            violations.add("jwt.secret (JWT_SECRET) is still the insecure default");
        }

        if (INSECURE_DB_PASSWORD.equals(dbPassword)) {
            violations.add("spring.datasource.password (DB_PASSWORD) is still the insecure default");
        }

        if (PLACEHOLDER_ARK_API_KEY.equals(arkApiKey)) {
            violations.add("volcengine.ark.api-key (VOLCENGINE_API_KEY) is still the placeholder default");
        }

        if (!violations.isEmpty()) {
            String msg = "Production safety check failed - insecure defaults detected:\n  - "
                    + String.join("\n  - ", violations);
            throw new IllegalStateException(msg);
        }

        log.info("Production safety check passed");
    }

    private boolean isProductionProfile() {
        return Arrays.stream(environment.getActiveProfiles())
                .anyMatch(p -> PRODUCTION_PROFILES.contains(p.toLowerCase()));
    }
}
