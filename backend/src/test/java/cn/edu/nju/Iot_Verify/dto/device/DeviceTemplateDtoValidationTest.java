package cn.edu.nju.Iot_Verify.dto.device;

import jakarta.validation.ConstraintViolation;
import jakarta.validation.Validation;
import jakarta.validation.Validator;
import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Bean Validation tests for DeviceTemplateDto.
 * Covers two fixed validation gaps:
 * 1. InternalVariable oneOf constraint (Values vs LowerBound+UpperBound)
 * 2. Dynamic cascade validation via @Valid on WorkingState.dynamics
 */
class DeviceTemplateDtoValidationTest {

    private final Validator validator = Validation.buildDefaultValidatorFactory().getValidator();

    // ── helpers ──

    private DeviceTemplateDto wrapManifest(DeviceTemplateDto.DeviceManifest manifest) {
        DeviceTemplateDto dto = new DeviceTemplateDto();
        dto.setName("TestTemplate");
        dto.setManifest(manifest);
        return dto;
    }

    private DeviceTemplateDto.DeviceManifest manifestWithInternalVar(DeviceTemplateDto.DeviceManifest.InternalVariable iv) {
        return DeviceTemplateDto.DeviceManifest.builder()
                .internalVariables(List.of(iv))
                .build();
    }

    private DeviceTemplateDto.DeviceManifest manifestWithDynamic(DeviceTemplateDto.DeviceManifest.Dynamic dynamic) {
        DeviceTemplateDto.DeviceManifest.WorkingState ws = DeviceTemplateDto.DeviceManifest.WorkingState.builder()
                .name("on")
                .dynamics(List.of(dynamic))
                .build();
        return DeviceTemplateDto.DeviceManifest.builder()
                .workingStates(List.of(ws))
                .build();
    }

    private DeviceTemplateDto.DeviceManifest manifestWithApi(DeviceTemplateDto.DeviceManifest.API api) {
        return DeviceTemplateDto.DeviceManifest.builder()
                .apis(List.of(api))
                .build();
    }

    private boolean hasViolationContaining(Set<? extends ConstraintViolation<?>> violations, String substring) {
        return violations.stream().anyMatch(v -> v.getMessage().contains(substring));
    }

    // ── InternalVariable oneOf constraint ──

    @Test
    void internalVar_onlyValues_shouldBeValid() {
        var iv = DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                .name("status")
                .values(List.of("on", "off"))
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifestWithInternalVar(iv)));
        assertFalse(hasViolationContaining(violations, "InternalVariable must explicitly define"));
    }

    @Test
    void internalVar_onlyRange_shouldBeValid() {
        var iv = DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                .name("temperature")
                .lowerBound(0)
                .upperBound(100)
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifestWithInternalVar(iv)));
        assertFalse(hasViolationContaining(violations, "InternalVariable must explicitly define"));
    }

    @Test
    void internalVar_neither_shouldRejectInsteadOfImplicitlyBecomingBoolean() {
        var iv = DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                .name("isActive")
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifestWithInternalVar(iv)));
        assertTrue(hasViolationContaining(violations, "InternalVariable must explicitly define"));
    }

    @Test
    void internalVar_valuesAndRange_shouldReject() {
        var iv = DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                .name("bad")
                .values(List.of("a", "b"))
                .lowerBound(0)
                .upperBound(10)
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifestWithInternalVar(iv)));
        assertTrue(hasViolationContaining(violations, "InternalVariable must explicitly define"));
    }

    @Test
    void internalVar_onlyLowerBound_shouldReject() {
        var iv = DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                .name("bad")
                .lowerBound(0)
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifestWithInternalVar(iv)));
        assertTrue(hasViolationContaining(violations, "InternalVariable must explicitly define"));
    }

    @Test
    void internalVar_onlyUpperBound_shouldReject() {
        var iv = DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                .name("bad")
                .upperBound(100)
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifestWithInternalVar(iv)));
        assertTrue(hasViolationContaining(violations, "InternalVariable must explicitly define"));
    }

    @Test
    void internalVar_valuesAndSingleBound_shouldReject() {
        var iv = DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                .name("bad")
                .values(List.of("x"))
                .lowerBound(0)
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifestWithInternalVar(iv)));
        assertTrue(hasViolationContaining(violations, "InternalVariable must explicitly define"));
    }

    // ── Dynamic cascade validation ──

    @Test
    void dynamic_onlyChangeRate_shouldBeValid() {
        var dyn = DeviceTemplateDto.DeviceManifest.Dynamic.builder()
                .variableName("temperature")
                .changeRate("-1")
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifestWithDynamic(dyn)));
        assertFalse(hasViolationContaining(violations, "Dynamic must have"));
    }

    @Test
    void dynamic_onlyValue_shouldBeValid() {
        var dyn = DeviceTemplateDto.DeviceManifest.Dynamic.builder()
                .variableName("status")
                .value("open")
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifestWithDynamic(dyn)));
        assertFalse(hasViolationContaining(violations, "Dynamic must have"));
    }

    @Test
    void dynamic_both_shouldReject() {
        var dyn = DeviceTemplateDto.DeviceManifest.Dynamic.builder()
                .variableName("bad")
                .changeRate("1")
                .value("open")
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifestWithDynamic(dyn)));
        assertTrue(hasViolationContaining(violations, "Dynamic must have"));
    }

    @Test
    void dynamic_neither_shouldReject() {
        var dyn = DeviceTemplateDto.DeviceManifest.Dynamic.builder()
                .variableName("bad")
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifestWithDynamic(dyn)));
        assertTrue(hasViolationContaining(violations, "Dynamic must have"));
    }

    @Test
    void dynamic_cascadeThroughFullDto_shouldReject() {
        // Verifies the @Valid cascade: DeviceTemplateDto → DeviceManifest → WorkingState → Dynamic
        var dyn = DeviceTemplateDto.DeviceManifest.Dynamic.builder()
                .variableName("bad")
                .changeRate("1")
                .value("open")
                .build();

        DeviceTemplateDto dto = wrapManifest(manifestWithDynamic(dyn));
        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(dto);
        assertTrue(hasViolationContaining(violations, "Dynamic must have"),
                "Dynamic validation must cascade through WorkingState.dynamics @Valid");
    }

    @Test
    void apiMissingStartState_shouldRejectInsteadOfImplicitlyAllowingAnyState() {
        var api = DeviceTemplateDto.DeviceManifest.API.builder()
                .name("turnOn")
                .endState("on")
                .signal(false)
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(
                wrapManifest(manifestWithApi(api)));

        assertTrue(hasViolationContaining(violations, "API StartState must explicitly define"));
    }

    @Test
    void apiEmptyStartState_shouldRemainAnExplicitAnyStateChoice() {
        var api = DeviceTemplateDto.DeviceManifest.API.builder()
                .name("turnOn")
                .startState("")
                .endState("on")
                .signal(false)
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(
                wrapManifest(manifestWithApi(api)));

        assertFalse(hasViolationContaining(violations, "API StartState must explicitly define"));
    }

    @Test
    void apiMissingSignal_shouldRejectInsteadOfImplicitlyBecomingCommandOnly() {
        var api = DeviceTemplateDto.DeviceManifest.API.builder()
                .name("turnOn")
                .startState("off")
                .endState("on")
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(
                wrapManifest(manifestWithApi(api)));

        assertTrue(hasViolationContaining(violations, "API Signal must explicitly choose"));
    }

    @Test
    void internalVariableMissingCompromiseChoice_shouldReject() {
        var variable = DeviceTemplateDto.DeviceManifest.InternalVariable.builder()
                .name("reading")
                .isInside(true)
                .values(List.of("normal", "alert"))
                .trust("trusted")
                .privacy("public")
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(
                wrapManifest(manifestWithInternalVar(variable)));

        assertTrue(hasViolationContaining(violations,
                "FalsifiableWhenCompromised must explicitly define"));
    }

    @Test
    void workingStateMissingSecurityLabels_shouldReject() {
        var state = DeviceTemplateDto.DeviceManifest.WorkingState.builder()
                .name("on")
                .build();
        var manifest = DeviceTemplateDto.DeviceManifest.builder()
                .workingStates(List.of(state))
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifest));

        assertTrue(hasViolationContaining(violations, "WorkingState Trust must be explicit"));
        assertTrue(hasViolationContaining(violations, "WorkingState Privacy must be explicit"));
    }

    @Test
    void contentPrivacyValidation_shouldCascadeThroughManifest() {
        var content = DeviceTemplateDto.DeviceManifest.Content.builder()
                .name("photo")
                .privacy("secret")
                .build();
        var manifest = DeviceTemplateDto.DeviceManifest.builder()
                .contents(List.of(content))
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifest));

        assertTrue(hasViolationContaining(violations, "Content Privacy must be public or private"));
    }

    @Test
    void environmentDomainSecurityLabels_shouldRejectInvalidValues() {
        var domain = DeviceTemplateDto.DeviceManifest.EnvironmentDomain.builder()
                .name("temperature")
                .lowerBound(0)
                .upperBound(100)
                .trust("unknown")
                .privacy("secret")
                .build();
        var manifest = DeviceTemplateDto.DeviceManifest.builder()
                .environmentDomains(List.of(domain))
                .build();

        Set<ConstraintViolation<DeviceTemplateDto>> violations = validator.validate(wrapManifest(manifest));

        assertTrue(hasViolationContaining(violations, "EnvironmentDomain Trust must be trusted or untrusted"));
        assertTrue(hasViolationContaining(violations, "EnvironmentDomain Privacy must be public or private"));
    }
}
