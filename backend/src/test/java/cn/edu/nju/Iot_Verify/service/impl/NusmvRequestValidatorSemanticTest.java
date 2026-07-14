package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvSpecificationBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.util.SmvConstants;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

class NusmvRequestValidatorSemanticTest {

    @Test
    void validateRuleSemantics_rejectsNonSignalApiConditionAndUnknownCommandApi() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1")
                        .attribute("turnOn")
                        .targetType("api")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("sensor_1")
                        .action("missingAction")
                        .build())
                .build();

        NusmvRequestValidator.validateRuleSemantics(List.of(rule), Map.of("sensor_1", smv()), errors);

        assertEquals("Unknown or non-signal API for rule condition: turnOn",
                errors.get("rules[0].conditions[0].attribute"));
        assertEquals("Unknown command API for device template: missingAction",
                errors.get("rules[0].command.action"));
    }

    @Test
    void validateRuleSemantics_rejectsContentOnAnActionWithoutContentCapability() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        DeviceSmvData model = smv();
        model.getManifest().setContents(List.of(DeviceManifest.Content.builder()
                .name("photo")
                .privacy("private")
                .build()));
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1")
                        .attribute("level")
                        .targetType("variable")
                        .relation(">")
                        .value("1")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("sensor_1")
                        .action("turnOn")
                        .contentDevice("sensor_1")
                        .content("photo")
                        .build())
                .build();

        NusmvRequestValidator.validateRuleSemantics(List.of(rule), Map.of("sensor_1", model), errors);

        assertEquals("Command API 'turnOn' does not accept a content-sensitivity input",
                errors.get("rules[0].command.content"));
    }

    @Test
    void validateSpecificationSemantics_rejectsInvalidApiPrivacyAndModeValues() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec1");
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        spec.setAConditions(new ArrayList<>(List.of(
                condition("api", "turnOn", "=", "TRUE"),
                propertyCondition("privacy", "state", "Mode", "=", "secret"),
                condition("mode", "Mode", "=", "missing")
        )));
        spec.setIfConditions(new ArrayList<>());
        spec.setThenConditions(new ArrayList<>());
        spec.setDevices(new ArrayList<>());

        NusmvRequestValidator.validateSpecificationSemantics(List.of(spec), Map.of("sensor_1", smv()), errors);

        assertEquals("Unknown or non-signal API for specification: turnOn",
                errors.get("specs[0].aConditions[0].key"));
        assertEquals("Value must be public or private: secret",
                errors.get("specs[0].aConditions[1].value"));
        assertTrue(errors.get("specs[0].aConditions[2].value")
                .contains("Illegal mode value 'missing'"));
    }

    @Test
    void validateSpecifications_rejectsMixedTemplateShape() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("sensor_1");
        device.setTemplateName("Sensor");
        SpecificationDto hiddenImplication = new SpecificationDto();
        hiddenImplication.setId("spec-hidden");
        hiddenImplication.setTemplateId("1");
        hiddenImplication.setTemplateLabel("Always");
        hiddenImplication.setAConditions(new ArrayList<>());
        hiddenImplication.setIfConditions(new ArrayList<>(List.of(condition("state", "state", "=", "on"))));
        hiddenImplication.setThenConditions(new ArrayList<>(List.of(condition("state", "state", "=", "off"))));
        hiddenImplication.setDevices(new ArrayList<>());

        NusmvRequestValidator.validateSpecifications(List.of(hiddenImplication), List.of(device), errors);

        assertEquals("Template 1 requires at least one A condition",
                errors.get("specs[0].aConditions"));
        assertEquals("Template 1 uses A conditions only",
                errors.get("specs[0].templateId"));
    }

    @Test
    void validateSpecifications_rejectsSafetyConditionsWhoseDerivedReliabilityIsAmbiguous() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        DeviceVerificationDto device = device("sensor_1", "Sensor");
        SpecificationDto safety = new SpecificationDto();
        safety.setId("safety-ambiguous");
        safety.setTemplateId("7");
        safety.setTemplateLabel("Untrusted input must not cause A");
        safety.setAConditions(new ArrayList<>(List.of(
                propertyCondition("privacy", "state", "Mode", "=", "private"),
                condition("state", "state", "!=", "off")
        )));
        safety.setIfConditions(new ArrayList<>());
        safety.setThenConditions(new ArrayList<>());
        safety.setDevices(new ArrayList<>());

        NusmvRequestValidator.validateSpecifications(List.of(safety), List.of(device), errors);

        assertTrue(errors.get("specs[0].aConditions[0].targetType")
                .contains("MEDIC control-source label is derived automatically"));
        assertTrue(errors.get("specs[0].aConditions[1].relation")
                .contains("require '='"));
    }

    @Test
    void validateSpecificationSemantics_rejectsSafetySignalWithoutModeledEndState() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        SpecificationDto safety = new SpecificationDto();
        safety.setId("safety-signal-without-end-state");
        safety.setTemplateId("7");
        safety.setAConditions(List.of(condition("api", "detected", "=", "TRUE")));
        safety.setIfConditions(new ArrayList<>());
        safety.setThenConditions(new ArrayList<>());

        NusmvRequestValidator.validateSpecificationSemantics(
                List.of(safety), Map.of("sensor_1", smv()), errors);

        assertTrue(errors.get("specs[0].aConditions[0].key").contains("has no EndState"));
    }

    @Test
    void validateSemantics_checksVariableValueDomains() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        RuleDto invalidEnumRule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor_1")
                        .attribute("fanMode")
                        .targetType("variable")
                        .relation("=")
                        .value("turbo")
                        .build()))
                .command(RuleDto.Command.builder()
                        .deviceName("sensor_1")
                        .action("turnOn")
                        .build())
                .build();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec2");
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        spec.setAConditions(new ArrayList<>(List.of(condition("variable", "level", ">", "9"))));
        spec.setIfConditions(new ArrayList<>());
        spec.setThenConditions(new ArrayList<>());
        spec.setDevices(new ArrayList<>());

        NusmvRequestValidator.validateRuleSemantics(List.of(invalidEnumRule), Map.of("sensor_1", smv()), errors);
        NusmvRequestValidator.validateSpecificationSemantics(List.of(spec), Map.of("sensor_1", smv()), errors);

        assertEquals("Illegal enum value for variable 'fanMode': turbo",
                errors.get("rules[0].conditions[0].value"));
        assertEquals("Variable value out of range for 'level': 9 (allowed 0..5)",
                errors.get("specs[0].aConditions[0].value"));
    }

    @Test
    void validateDeviceSemantics_rejectsStateFieldsForNoModeDevices() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("smoke_1");
        device.setTemplateName("Smoke Sensor");
        device.setState("Working");
        device.setCurrentStateTrust("trusted");
        device.setCurrentStatePrivacy("private");

        NusmvRequestValidator.validateDeviceSemantics(List.of(device), Map.of("smoke_1", noModeSmv()), errors);

        assertEquals("No-mode devices must omit state in model requests",
                errors.get("devices[0].state"));
        assertEquals("currentStateTrust is only valid for device templates with modes",
                errors.get("devices[0].currentStateTrust"));
        assertEquals("currentStatePrivacy is only valid for device templates with modes",
                errors.get("devices[0].currentStatePrivacy"));
    }

    @Test
    void validateDeviceSemantics_rejectsInvalidRuntimeOverrides() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("sensor_1");
        device.setTemplateName("Sensor");
        device.setState("missing");
        device.setCurrentStateTrust("maybe");
        device.setCurrentStatePrivacy("secret");
        device.setVariables(List.of(
                new VariableStateDto("Mode", "on", "trusted"),
                new VariableStateDto("level", "9", "maybe")));
        device.setPrivacies(List.of(
                new PrivacyStateDto("missing", "secret"),
                new PrivacyStateDto("temperature", "private"),
                new PrivacyStateDto("temperature", "public")));

        NusmvRequestValidator.validateDeviceSemantics(List.of(device), Map.of("sensor_1", smv()), errors);

        assertEquals("Illegal state value for device template: missing",
                errors.get("devices[0].state"));
        assertEquals("Value must be trusted or untrusted: maybe",
                errors.get("devices[0].currentStateTrust"));
        assertEquals("Value must be public or private: secret",
                errors.get("devices[0].currentStatePrivacy"));
        assertEquals("Unknown runtime variable for device template: Mode",
                errors.get("devices[0].variables[0].name"));
        assertEquals("Variable value out of range for 'level': 9 (allowed 0..5)",
                errors.get("devices[0].variables[1].value"));
        assertEquals("Value must be trusted or untrusted: maybe",
                errors.get("devices[0].variables[1].trust"));
        assertEquals("Value must be public or private: secret",
                errors.get("devices[0].privacies[0].privacy"));
        assertEquals("Unknown device-local variable privacy target: missing",
                errors.get("devices[0].privacies[0].name"));
        assertEquals("Duplicate privacy override: temperature",
                errors.get("devices[0].privacies[2].name"));
    }

    @Test
    void validateDeviceSemantics_keepsStatePrivacySeparateFromLocalVariablePrivacies() {
        Map<String, String> validErrors = NusmvRequestValidator.newErrors();
        DeviceVerificationDto valid = new DeviceVerificationDto();
        valid.setVarName("sensor_1");
        valid.setTemplateName("Sensor");
        valid.setState("on");
        valid.setCurrentStatePrivacy("private");

        NusmvRequestValidator.validateDeviceSemantics(List.of(valid), Map.of("sensor_1", smv()), validErrors);

        assertTrue(validErrors.isEmpty(), () -> "Expected state privacy to be valid: " + validErrors);

        Map<String, String> generatedKeyErrors = NusmvRequestValidator.newErrors();
        DeviceVerificationDto generatedKey = new DeviceVerificationDto();
        generatedKey.setVarName("sensor_1");
        generatedKey.setTemplateName("Sensor");
        generatedKey.setState("on");
        generatedKey.setPrivacies(List.of(new PrivacyStateDto("Mode_on", "private")));

        NusmvRequestValidator.validateDeviceSemantics(
                List.of(generatedKey), Map.of("sensor_1", smv()), generatedKeyErrors);

        assertEquals("Unknown device-local variable privacy target: Mode_on",
                generatedKeyErrors.get("devices[0].privacies[0].name"));
    }

    @Test
    void validateDeviceSemantics_rejectsEnvironmentOverridesOnDeviceInstances() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("sensor_1");
        device.setTemplateName("Temperature Sensor");
        device.setVariables(List.of(new VariableStateDto("temperature", "28", "trusted")));
        device.setPrivacies(List.of(new PrivacyStateDto("temperature", "public")));

        NusmvRequestValidator.validateDeviceSemantics(List.of(device), Map.of("sensor_1", envSmv()), errors);

        assertEquals("Environment variable must be supplied through environmentVariables: temperature",
                errors.get("devices[0].variables[0].name"));
        assertEquals("Environment variable privacy must be supplied through environmentVariables: temperature",
                errors.get("devices[0].privacies[0].name"));
    }

    @Test
    void validateEnvironmentVariables_usesBoardPoolAsRequiredAuthority() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();

        NusmvRequestValidator.validateEnvironmentVariables(
                List.of(new BoardEnvironmentVariableDto("temperature", "28", "trusted", "public")),
                Map.of("sensor_1", envSmv()),
                errors);

        assertTrue(errors.isEmpty(), () -> "Expected environment pool to validate, got: " + errors);
    }

    @Test
    void validateEnvironmentOverrides_rejectsDuplicatesBeforeDefaultMerging() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();

        NusmvRequestValidator.validateEnvironmentVariableOverrides(
                List.of(
                        new BoardEnvironmentVariableDto("temperature", "20", "trusted", "public"),
                        new BoardEnvironmentVariableDto("temperature", "30", "untrusted", "private")),
                Map.of("sensor_1", envSmv()),
                errors);

        assertEquals("Duplicate environment variable: temperature",
                errors.get("environmentVariables[1].name"));
    }

    @Test
    void validateEnvironmentOverrides_rejectsExplicitBlankLabelsInsteadOfUsingTemplateDefaults() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();

        NusmvRequestValidator.validateEnvironmentVariableOverrides(
                List.of(new BoardEnvironmentVariableDto("temperature", " ", " ", "")),
                Map.of("sensor_1", envSmv()),
                errors);

        assertTrue(errors.get("environmentVariables[0].trust").contains("trusted or untrusted"));
        assertTrue(errors.get("environmentVariables[0].privacy").contains("public or private"));
        assertEquals("Environment variable value cannot be blank when provided",
                errors.get("environmentVariables[0].value"));
    }

    @Test
    void validateDeviceSemantics_rejectsExplicitBlankSecurityLabels() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        DeviceVerificationDto device = device("sensor_1", "Sensor");
        device.setState("on");
        device.setCurrentStateTrust(" ");
        device.setCurrentStatePrivacy("");
        device.setVariables(List.of(new VariableStateDto("level", "2", " ")));

        NusmvRequestValidator.validateDeviceSemantics(
                List.of(device), Map.of("sensor_1", smv()), errors);

        assertTrue(errors.get("devices[0].currentStateTrust").contains("trusted or untrusted"));
        assertTrue(errors.get("devices[0].currentStatePrivacy").contains("public or private"));
        assertTrue(errors.get("devices[0].variables[0].trust").contains("trusted or untrusted"));
    }

    @Test
    void validateDeviceSemantics_rejectsNullRuntimeOverrideItemsInsteadOfDroppingThem() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        DeviceVerificationDto device = device("sensor_1", "Sensor");
        List<VariableStateDto> variables = new ArrayList<>();
        variables.add(null);
        List<PrivacyStateDto> privacies = new ArrayList<>();
        privacies.add(null);
        device.setVariables(variables);
        device.setPrivacies(privacies);

        NusmvRequestValidator.validateDeviceSemantics(
                List.of(device), Map.of("sensor_1", smv()), errors);

        assertEquals("Variable item cannot be null", errors.get("devices[0].variables[0]"));
        assertEquals("Privacy item cannot be null", errors.get("devices[0].privacies[0]"));
    }

    @Test
    void validateMainNamespace_rejectsDeviceNameThatCollidesWithGeneratedEnvironmentIdentifier() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        DeviceSmvData smv = envSmv();
        smv.setVarName("a_temperature");

        NusmvRequestValidator.validateMainNamespace(
                List.of(device("a_temperature", "Temperature Sensor")),
                List.of(),
                Map.of("a_temperature", smv),
                false,
                errors);

        assertTrue(errors.get("environmentVariables").contains("a_temperature"));
        assertTrue(errors.get("environmentVariables").contains("device instance"));
    }

    @Test
    void validateAttackHasModeledEffect_rejectsACompromiseFlagWithNoBehavioralEffect() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();

        NusmvRequestValidator.validateAttackHasModeledEffect(
                true, List.of(), Map.of("sensor_1", smv()), errors);

        assertTrue(errors.get("isAttack").contains("would not change this model"));
        assertTrue(errors.get("isAttack").contains("FalsifiableWhenCompromised"));
    }

    @Test
    void validateAttackHasModeledEffect_acceptsADeclaredReadingOrAutomationLink() {
        DeviceSmvData falsifiableSmv = envSmv();
        falsifiableSmv.getVariables().get(0).setFalsifiableWhenCompromised(true);
        Map<String, String> readingErrors = NusmvRequestValidator.newErrors();
        NusmvRequestValidator.validateAttackHasModeledEffect(
                true, List.of(), Map.of("sensor_1", falsifiableSmv), readingErrors);
        assertTrue(readingErrors.isEmpty());

        Map<String, String> linkErrors = NusmvRequestValidator.newErrors();
        NusmvRequestValidator.validateAttackHasModeledEffect(
                true, List.of(RuleDto.builder().build()), Map.of("sensor_1", smv()), linkErrors);
        assertTrue(linkErrors.isEmpty());
    }

    @Test
    void validateMainNamespace_rejectsDeviceNameThatCollidesWithInternalAttackCounter() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        DeviceSmvData smv = smv();
        smv.setVarName(SmvConstants.NUSMV_COMPROMISED_POINT_COUNT);

        NusmvRequestValidator.validateMainNamespace(
                List.of(device(SmvConstants.NUSMV_COMPROMISED_POINT_COUNT, "Sensor")),
                List.of(),
                Map.of(SmvConstants.NUSMV_COMPROMISED_POINT_COUNT, smv),
                true,
                errors);

        assertTrue(errors.get("devices[0].varName").contains(SmvConstants.NUSMV_COMPROMISED_POINT_COUNT));
        assertTrue(errors.get("devices[0].varName").contains("generated compromised-point counter"));
    }

    @Test
    void validateMainNamespace_rejectsDeviceNameThatCollidesWithRuleExecutionMarker() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        String name = SmvConstants.RULE_EXECUTION_PROBE_PREFIX + "0";
        DeviceSmvData smv = smv();
        smv.setVarName(name);

        NusmvRequestValidator.validateMainNamespace(
                List.of(device(name, "Sensor")),
                List.of(RuleDto.builder().build()),
                Map.of(name, smv),
                false,
                errors);

        assertTrue(errors.get("rules[0]").contains("generated rule execution marker"));
        assertTrue(errors.get("rules[0]").contains("device instance"));
    }

    @Test
    void validateMainNamespace_rejectsDeviceNameThatCollidesWithAutomationLinkAttackChoice() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        String name = SmvConstants.AUTOMATION_LINK_ATTACK_PREFIX + "0";
        DeviceSmvData smv = smv();
        smv.setVarName(name);

        NusmvRequestValidator.validateMainNamespace(
                List.of(device(name, "Sensor")),
                List.of(RuleDto.builder().build()),
                Map.of(name, smv),
                true,
                errors);

        assertTrue(errors.get("rules[0]").contains("generated automation-link attack choice"));
        assertTrue(errors.get("rules[0]").contains("device instance"));
    }

    @Test
    void validateSpecificationSemantics_rejectsLegacyGeneratedEnvironmentAliasWhenNoLiteralVariableExists() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec-env-prefix");
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        spec.setAConditions(new ArrayList<>(List.of(condition("variable", "a_temperature", ">", "28"))));
        spec.setIfConditions(new ArrayList<>());
        spec.setThenConditions(new ArrayList<>());
        spec.setDevices(new ArrayList<>());

        NusmvRequestValidator.validateSpecificationSemantics(List.of(spec), Map.of("sensor_1", envSmv()), errors);

        assertEquals("Unknown internal or environment variable for specification: a_temperature",
                errors.get("specs[0].aConditions[0].key"));
    }

    @Test
    void validateSpecificationSemantics_acceptsLiteralAPrefixedEnvironmentVariableName() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec-env-literal-prefix");
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        spec.setAConditions(new ArrayList<>(List.of(condition("variable", "a_temperature", ">", "28"))));
        spec.setIfConditions(new ArrayList<>());
        spec.setThenConditions(new ArrayList<>());
        spec.setDevices(new ArrayList<>());

        NusmvRequestValidator.validateSpecificationSemantics(
                List.of(spec),
                Map.of("sensor_1", aPrefixedEnvSmv()),
                errors);

        assertTrue(errors.isEmpty(), () -> "Expected literal a_ variable name to validate, got: " + errors);
    }

    @Test
    void specificationBuilder_generatesNuSmvPrefixForLiteralAPrefixedEnvironmentName() {
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec-env-literal-prefix");
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        spec.setAConditions(new ArrayList<>(List.of(condition("variable", "a_temperature", ">", "28"))));
        spec.setIfConditions(new ArrayList<>());
        spec.setThenConditions(new ArrayList<>());
        spec.setDevices(new ArrayList<>());

        String smvText = new SmvSpecificationBuilder()
                .build(List.of(spec), false, 3, Map.of("sensor_1", aPrefixedEnvSmv()), false);

        assertTrue(smvText.contains("a_a_temperature>28"), smvText);
    }

    @Test
    void validateSpecificationSemantics_rejectsGeneratedTrustAliasWhenNoLiteralKeyExists() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec-trust-prefix");
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        spec.setAConditions(new ArrayList<>(List.of(
                propertyCondition("trust", "variable", "trust_temperature", "=", "untrusted"))));
        spec.setIfConditions(new ArrayList<>());
        spec.setThenConditions(new ArrayList<>());
        spec.setDevices(new ArrayList<>());

        NusmvRequestValidator.validateSpecificationSemantics(List.of(spec), Map.of("sensor_1", envSmv()), errors);

        assertEquals("Unknown property variable for specification: trust_temperature",
                errors.get("specs[0].aConditions[0].key"));
    }

    @Test
    void specificationBuilder_treatsGeneratedTrustPrefixAsLiteralVariableName() {
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec-trust-literal-prefix");
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        spec.setAConditions(new ArrayList<>(List.of(
                propertyCondition("trust", "variable", "trust_temperature", "=", "untrusted"))));
        spec.setIfConditions(new ArrayList<>());
        spec.setThenConditions(new ArrayList<>());
        spec.setDevices(new ArrayList<>());

        String smvText = new SmvSpecificationBuilder()
                .build(List.of(spec), false, 3, Map.of("sensor_1", trustPrefixedLocalSmv()), false);

        assertTrue(smvText.contains("sensor_1.trust_trust_temperature=untrusted"), smvText);
    }

    @Test
    void validateEnvironmentVariables_rejectsUnknownMissingAndInvalidPoolValues() {
        Map<String, String> errors = NusmvRequestValidator.newErrors();

        NusmvRequestValidator.validateEnvironmentVariables(
                List.of(
                        new BoardEnvironmentVariableDto("unknown", "1", "trusted", "public"),
                        new BoardEnvironmentVariableDto("temperature", "99", "maybe", "secret")
                ),
                Map.of("sensor_1", envSmv()),
                errors);

        assertEquals("Environment variable is not required by the current board: unknown",
                errors.get("environmentVariables[0].name"));
        assertEquals("Value must be trusted or untrusted: maybe",
                errors.get("environmentVariables[1].trust"));
        assertEquals("Value must be public or private: secret",
                errors.get("environmentVariables[1].privacy"));
        assertEquals("Variable value out of range for 'temperature': 99 (allowed 0..50)",
                errors.get("environmentVariables[1].value"));
    }


    @Test
    void specificationBuilder_cleansEnumVariableValuesWithSpaces() {
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec3");
        spec.setTemplateId("1");
        spec.setTemplateLabel("Always");
        spec.setAConditions(new ArrayList<>(List.of(condition("variable", "fanMode", "=", "fan only"))));
        spec.setIfConditions(new ArrayList<>());
        spec.setThenConditions(new ArrayList<>());
        spec.setDevices(new ArrayList<>());

        String smvText = new SmvSpecificationBuilder()
                .build(List.of(spec), false, 3, Map.of("sensor_1", smv()), false);

        assertTrue(smvText.contains("sensor_1.fanMode=fanonly"));
    }

    private static SpecConditionDto condition(String targetType, String key, String relation, String value) {
        SpecConditionDto condition = new SpecConditionDto();
        condition.setSide("a");
        condition.setDeviceId("sensor_1");
        condition.setDeviceLabel("Sensor");
        condition.setTargetType(targetType);
        condition.setKey(key);
        condition.setRelation(relation);
        condition.setValue(value);
        return condition;
    }

    private static SpecConditionDto propertyCondition(String targetType,
                                                      String propertyScope,
                                                      String key,
                                                      String relation,
                                                      String value) {
        SpecConditionDto condition = condition(targetType, key, relation, value);
        condition.setPropertyScope(propertyScope);
        return condition;
    }

    private static DeviceSmvData smv() {
        DeviceManifest.InternalVariable variable = DeviceManifest.InternalVariable.builder()
                .name("temperature")
                .isInside(true)
                .build();
        DeviceManifest.InternalVariable fanMode = DeviceManifest.InternalVariable.builder()
                .name("fanMode")
                .isInside(true)
                .values(List.of("fan only", "idle"))
                .build();
        DeviceManifest.InternalVariable level = DeviceManifest.InternalVariable.builder()
                .name("level")
                .isInside(true)
                .lowerBound(0)
                .upperBound(5)
                .build();
        DeviceManifest.API signalApi = DeviceManifest.API.builder()
                .name("detected")
                .signal(true)
                .build();
        DeviceManifest.API actionApi = DeviceManifest.API.builder()
                .name("turnOn")
                .signal(false)
                .build();
        DeviceManifest manifest = DeviceManifest.builder()
                .name("Sensor")
                .modes(List.of("Mode"))
                .internalVariables(List.of(variable, fanMode, level))
                .apis(List.of(signalApi, actionApi))
                .build();

        DeviceSmvData smv = new DeviceSmvData();
        smv.setManifest(manifest);
        smv.setVarName("sensor_1");
        smv.setTemplateName("Sensor");
        smv.setModes(List.of("Mode"));
        smv.setModeStates(new LinkedHashMap<>(Map.of("Mode", List.of("on", "off"))));
        smv.setVariables(List.of(variable, fanMode, level));
        return smv;
    }

    private static DeviceSmvData noModeSmv() {
        DeviceManifest manifest = DeviceManifest.builder()
                .name("Smoke Sensor")
                .modes(List.of())
                .internalVariables(List.of(DeviceManifest.InternalVariable.builder()
                        .name("smoke")
                        .isInside(false)
                        .values(List.of("clear", "detected"))
                        .build()))
                .build();

        DeviceSmvData smv = new DeviceSmvData();
        smv.setManifest(manifest);
        smv.setVarName("smoke_1");
        smv.setTemplateName("Smoke Sensor");
        smv.setModes(List.of());
        smv.setVariables(manifest.getInternalVariables());
        return smv;
    }

    private static DeviceSmvData envSmv() {
        DeviceManifest.InternalVariable temperature = DeviceManifest.InternalVariable.builder()
                .name("temperature")
                .isInside(false)
                .lowerBound(0)
                .upperBound(50)
                .trust("trusted")
                .privacy("public")
                .build();
        DeviceManifest manifest = DeviceManifest.builder()
                .name("Temperature Sensor")
                .modes(List.of())
                .internalVariables(List.of(temperature))
                .build();

        DeviceSmvData smv = new DeviceSmvData();
        smv.setManifest(manifest);
        smv.setVarName("sensor_1");
        smv.setTemplateName("Temperature Sensor");
        smv.setModes(List.of());
        smv.setVariables(manifest.getInternalVariables());
        smv.setEnvVariables(Map.of("temperature", temperature));
        return smv;
    }

    private static DeviceSmvData aPrefixedEnvSmv() {
        DeviceManifest.InternalVariable temperature = DeviceManifest.InternalVariable.builder()
                .name("a_temperature")
                .isInside(false)
                .lowerBound(0)
                .upperBound(50)
                .trust("trusted")
                .privacy("public")
                .build();
        DeviceManifest manifest = DeviceManifest.builder()
                .name("Temperature Sensor")
                .modes(List.of())
                .internalVariables(List.of(temperature))
                .build();

        DeviceSmvData smv = new DeviceSmvData();
        smv.setManifest(manifest);
        smv.setVarName("sensor_1");
        smv.setTemplateName("Temperature Sensor");
        smv.setModes(List.of());
        smv.setVariables(manifest.getInternalVariables());
        smv.setEnvVariables(Map.of("a_temperature", temperature));
        return smv;
    }

    private static DeviceSmvData trustPrefixedLocalSmv() {
        DeviceManifest.InternalVariable variable = DeviceManifest.InternalVariable.builder()
                .name("trust_temperature")
                .isInside(true)
                .lowerBound(0)
                .upperBound(50)
                .trust("trusted")
                .privacy("public")
                .build();
        DeviceManifest manifest = DeviceManifest.builder()
                .name("Sensor")
                .modes(List.of())
                .internalVariables(List.of(variable))
                .build();

        DeviceSmvData smv = new DeviceSmvData();
        smv.setManifest(manifest);
        smv.setVarName("sensor_1");
        smv.setTemplateName("Sensor");
        smv.setModes(List.of());
        smv.setVariables(manifest.getInternalVariables());
        return smv;
    }

    private static DeviceVerificationDto device(String varName, String templateName) {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName(varName);
        device.setTemplateName(templateName);
        return device;
    }
}
