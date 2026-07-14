package cn.edu.nju.Iot_Verify.configure;

import org.junit.jupiter.api.Test;
import org.springframework.mock.env.MockEnvironment;
import org.springframework.test.util.ReflectionTestUtils;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

class ProductionSafetyCheckTest {

    @Test
    void check_nonProductionProfile_allowsDevelopmentDefaults() {
        ProductionSafetyCheck check = checkWith(
                environment(),
                "iot-verify-secret-key-must-be-at-least-256-bits-long-for-hs256",
                "sharkdingo123",
                "your_api_key_here");

        assertDoesNotThrow(check::check);
    }

    @Test
    void check_productionProfile_rejectsUnsafeDefaults() {
        ProductionSafetyCheck check = checkWith(
                environment("prod"),
                "iot-verify-secret-key-must-be-at-least-256-bits-long-for-hs256",
                "sharkdingo123",
                "your_api_key_here");

        IllegalStateException ex = assertThrows(IllegalStateException.class, check::check);
        assertTrue(ex.getMessage().contains("jwt.secret"));
        assertTrue(ex.getMessage().contains("spring.datasource.password"));
        assertTrue(ex.getMessage().contains("llm.api-key"));
    }

    @Test
    void check_productionProfile_allowsOverriddenSecrets() {
        ProductionSafetyCheck check = checkWith(
                environment("production"),
                "a-real-production-secret-that-is-long-enough-for-hs256",
                "non-default-password",
                "sk-live-value");

        assertDoesNotThrow(check::check);
    }

    private static MockEnvironment environment(String... profiles) {
        MockEnvironment environment = new MockEnvironment();
        environment.setActiveProfiles(profiles);
        return environment;
    }

    private static ProductionSafetyCheck checkWith(MockEnvironment environment,
                                                   String jwtSecret,
                                                   String dbPassword,
                                                   String llmApiKey) {
        ProductionSafetyCheck check = new ProductionSafetyCheck(environment);
        ReflectionTestUtils.setField(check, "jwtSecret", jwtSecret);
        ReflectionTestUtils.setField(check, "dbPassword", dbPassword);
        ReflectionTestUtils.setField(check, "llmApiKey", llmApiKey);
        return check;
    }
}
