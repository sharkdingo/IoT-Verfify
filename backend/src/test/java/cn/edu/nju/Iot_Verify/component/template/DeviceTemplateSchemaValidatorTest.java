package cn.edu.nju.Iot_Verify.component.template;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.fasterxml.jackson.databind.node.ObjectNode;
import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;

class DeviceTemplateSchemaValidatorTest {

    private final ObjectMapper objectMapper = new ObjectMapper();
    private final DeviceTemplateSchemaValidator validator = new DeviceTemplateSchemaValidator(objectMapper);

    @Test
    void defaultTemplates_matchCanonicalSchema() throws Exception {
        Path templateDir = Path.of("src/main/resources/deviceTemplate");
        List<Path> templates;
        try (Stream<Path> stream = Files.list(templateDir)) {
            templates = stream
                    .filter(path -> path.getFileName().toString().endsWith(".json"))
                    .sorted()
                    .toList();
        }

        assertFalse(templates.isEmpty(), "default templates should exist");
        for (Path template : templates) {
            JsonNode manifest = objectMapper.readTree(template.toFile());
            String name = manifest.path("Name").asText(template.getFileName().toString());
            assertDoesNotThrow(
                    () -> validator.validateRawManifest(name, manifest),
                    () -> "Template should match backend/device-template-schema.json: " + template);
        }
    }

    @Test
    void defaultControlSourceLabels_distinguishExternalInputsFromInHouseAction() throws Exception {
        JsonNode clock = objectMapper.readTree(
                Path.of("src/main/resources/deviceTemplate/Clock.json").toFile());
        JsonNode calendar = objectMapper.readTree(
                Path.of("src/main/resources/deviceTemplate/Calendar.json").toFile());
        JsonNode motion = objectMapper.readTree(
                Path.of("src/main/resources/deviceTemplate/Motion Detector.json").toFile());

        assertEquals("untrusted", clock.path("InternalVariables").get(0).path("Trust").asText());
        assertEquals("untrusted", calendar.path("InternalVariables").get(0).path("Trust").asText());
        assertEquals("untrusted", calendar.path("InternalVariables").get(1).path("Trust").asText());
        assertEquals("trusted", motion.path("InternalVariables").get(0).path("Trust").asText());

        assertVariableTrust("Car", "location", "untrusted");
        assertVariableTrust("Door RFID", "RFID", "untrusted");
        assertVariableTrust("Email", "receiveKey", "untrusted");
        assertVariableTrust("Email", "receiveMail", "untrusted");
        assertVariableTrust("Garage Door", "contact", "untrusted");
        assertVariableTrust("Mobile Phone", "location", "untrusted");
        assertVariableTrust("Mobile Phone", "steps", "untrusted");
        assertVariableTrust("Window", "contact", "untrusted");
    }

    @Test
    void defaultContentCapabilities_areDeclaredOnlyOnContentCarryingActions() throws Exception {
        JsonNode email = objectMapper.readTree(
                Path.of("src/main/resources/deviceTemplate/Email.json").toFile());
        JsonNode twitter = objectMapper.readTree(
                Path.of("src/main/resources/deviceTemplate/Twitter.json").toFile());
        JsonNode light = objectMapper.readTree(
                Path.of("src/main/resources/deviceTemplate/Light.json").toFile());

        assertEquals(true, email.path("APIs").get(0).path("AcceptsContent").asBoolean());
        assertEquals(true, twitter.path("APIs").get(0).path("AcceptsContent").asBoolean());
        assertFalse(light.path("APIs").get(0).path("AcceptsContent").asBoolean(false));
    }

    @Test
    void unknownFields_areRejectedByCanonicalSchema() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Debug Sensor",
                  "Unexpected": true
                }
                """);

        BadRequestException ex = assertThrows(BadRequestException.class,
                () -> validator.validateRawManifest("Debug Sensor", manifest));

        org.assertj.core.api.Assertions.assertThat(ex.getMessage())
                .contains("backend/device-template-schema.json")
                .contains("Unexpected");
    }

    @Test
    void securityLabelsRejectUppercaseInsteadOfSilentlyNormalizing() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Security Labels",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [{
                    "Name": "off",
                    "Trust": "trusted",
                    "Privacy": "public"
                  }],
                  "InternalVariables": [{
                    "Name": "reading",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "Values": ["ready", "busy"]
                  }],
                  "Contents": [{"Name": "status", "Privacy": "public"}]
                }
                """);
        assertDoesNotThrow(() -> validator.validateRawManifest("Security Labels", manifest));

        JsonNode uppercaseStateTrust = manifest.deepCopy();
        ((ObjectNode) uppercaseStateTrust.path("WorkingStates").get(0)).put("Trust", "Trusted");
        JsonNode uppercaseStatePrivacy = manifest.deepCopy();
        ((ObjectNode) uppercaseStatePrivacy.path("WorkingStates").get(0)).put("Privacy", "Public");
        JsonNode uppercaseVariableTrust = manifest.deepCopy();
        ((ObjectNode) uppercaseVariableTrust.path("InternalVariables").get(0)).put("Trust", "Untrusted");
        JsonNode uppercaseVariablePrivacy = manifest.deepCopy();
        ((ObjectNode) uppercaseVariablePrivacy.path("InternalVariables").get(0)).put("Privacy", "Private");
        JsonNode uppercaseContentPrivacy = manifest.deepCopy();
        ((ObjectNode) uppercaseContentPrivacy.path("Contents").get(0)).put("Privacy", "Private");

        for (JsonNode uppercaseManifest : List.of(
                uppercaseStateTrust,
                uppercaseStatePrivacy,
                uppercaseVariableTrust,
                uppercaseVariablePrivacy,
                uppercaseContentPrivacy)) {
            BadRequestException exception = assertThrows(BadRequestException.class,
                    () -> validator.validateRawManifest("Security Labels", uppercaseManifest));
            org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                    .contains("backend/device-template-schema.json");
        }
    }

    @Test
    void internalVariableScopeMustBeExplicitInsteadOfDefaultingToSharedEnvironment() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Ambiguous Sensor",
                  "InternalVariables": [{
                    "Name": "reading",
                    "FalsifiableWhenCompromised": true,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "LowerBound": 0,
                    "UpperBound": 100
                  }]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class,
                () -> validator.validateRawManifest("Ambiguous Sensor", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("IsInside");
    }

    @Test
    void internalVariableDomainMustBeExplicitInsteadOfDefaultingToBoolean() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Implicit Boolean Sensor",
                  "InternalVariables": [{
                    "Name": "detected",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": true,
                    "Trust": "trusted",
                    "Privacy": "public"
                  }]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class,
                () -> validator.validateRawManifest("Implicit Boolean Sensor", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("Values")
                .contains("LowerBound");
    }

    @Test
    void initialStateMustBeOneConcreteWorkingState() throws Exception {
        JsonNode wildcard = objectMapper.readTree("""
                {
                  "Name": "Ambiguous Mode Device",
                  "Modes": ["Power", "Profile"],
                  "InitState": "on;_",
                  "WorkingStates": [
                    {"Name": "on;normal", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "off;normal", "Trust": "trusted", "Privacy": "public"}
                  ]
                }
                """);
        BadRequestException wildcardException = assertThrows(BadRequestException.class,
                () -> validator.validateRawManifest("Ambiguous Mode Device", wildcard));
        org.assertj.core.api.Assertions.assertThat(wildcardException.getMessage())
                .contains("InitState 'on;_'")
                .contains("concrete value");

        JsonNode unknown = wildcard.deepCopy();
        ((com.fasterxml.jackson.databind.node.ObjectNode) unknown).put("InitState", "on;eco");
        BadRequestException unknownException = assertThrows(BadRequestException.class,
                () -> validator.validateRawManifest("Ambiguous Mode Device", unknown));
        org.assertj.core.api.Assertions.assertThat(unknownException.getMessage())
                .contains("InitState 'on;eco'")
                .contains("not defined in WorkingStates");

        JsonNode caseAlias = wildcard.deepCopy();
        ((com.fasterxml.jackson.databind.node.ObjectNode) caseAlias).put("InitState", "On;normal");
        BadRequestException caseException = assertThrows(BadRequestException.class,
                () -> validator.validateRawManifest("Ambiguous Mode Device", caseAlias));
        org.assertj.core.api.Assertions.assertThat(caseException.getMessage())
                .contains("InitState 'On;normal'")
                .contains("not defined in WorkingStates");
    }

    @Test
    void canonicalSerialization_omitsNestedNullsAndRemainsSchemaValid() throws Exception {
        DeviceManifest manifest = DeviceManifest.builder()
                .name("Temperature Sensor")
                .modes(List.of("Detection"))
                .initState("ready")
                .workingStates(List.of(DeviceManifest.WorkingState.builder()
                        .name("ready")
                        .trust("trusted")
                        .privacy("public")
                        .build()))
                .internalVariables(List.of(DeviceManifest.InternalVariable.builder()
                        .name("temperature")
                        .isInside(false)
                        .falsifiableWhenCompromised(true)
                        .trust("trusted")
                        .privacy("private")
                        .lowerBound(0)
                        .upperBound(100)
                        .build()))
                .build();

        String canonicalJson = validator.toCanonicalJson(manifest);
        JsonNode canonicalNode = objectMapper.readTree(canonicalJson);

        org.assertj.core.api.Assertions.assertThat(canonicalJson).doesNotContain(":null");
        assertDoesNotThrow(() -> validator.validateRawManifest("Temperature Sensor", canonicalNode));
    }

    @Test
    void dtoManifestValidation_treatsNullOptionalNestedFieldsAsOmitted() {
        DeviceManifest manifest = new DeviceManifest();
        manifest.setName("Lamp");
        manifest.setModes(List.of("LampState"));
        manifest.setInitState("off");

        DeviceManifest.WorkingState off = new DeviceManifest.WorkingState();
        off.setName("off");
        off.setTrust("trusted");
        off.setPrivacy("public");
        DeviceManifest.WorkingState on = new DeviceManifest.WorkingState();
        on.setName("on");
        on.setTrust("trusted");
        on.setPrivacy("public");
        manifest.setWorkingStates(List.of(off, on));

        assertDoesNotThrow(
                () -> validator.validateManifest("Lamp", manifest),
                "DTO validation should be equivalent to validating raw JSON with omitted optional fields");
    }

    @Test
    void apiTrigger_isRejectedByCanonicalSchema() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Lamp",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [
                    {"Name": "off", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "on", "Trust": "trusted", "Privacy": "public"}
                  ],
                  "APIs": [
                    {
                      "Name": "turn_on",
                      "EndState": "on",
                      "Trigger": {
                        "Attribute": "LampState",
                        "Relation": "=",
                        "Value": "off"
                      }
                    }
                  ]
                }
                """);

        BadRequestException ex = assertThrows(BadRequestException.class,
                () -> validator.validateRawManifest("Lamp", manifest));

        org.assertj.core.api.Assertions.assertThat(ex.getMessage())
                .contains("backend/device-template-schema.json")
                .contains("Trigger");
    }

    @Test
    void apiAssignments_areRejectedInsteadOfSilentlyIgnored() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Lamp",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [
                    {"Name": "off", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "on", "Trust": "trusted", "Privacy": "public"}
                  ],
                  "InternalVariables": [{
                    "Name": "level",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "LowerBound": 0,
                    "UpperBound": 100
                  }],
                  "APIs": [{
                    "Name": "turn_on",
                    "EndState": "on",
                    "Assignments": [{"Attribute": "level", "Value": "100"}]
                  }]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Lamp", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("unsupported Assignments field")
                .contains("triggered Transition");
    }

    @Test
    void apiOnStatelessTemplate_isRejectedAsUnrepresentable() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Stateless Service",
                  "APIs": [{"Name": "notify", "EndState": "sent"}]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Stateless Service", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("APIs require at least one Mode")
                .contains("modeled as a state change");
    }

    @Test
    void apiEndState_mustChangeAtLeastOneMode() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Dual Mode Device",
                  "Modes": ["Power", "Profile"],
                  "InitState": "off;idle",
                  "WorkingStates": [{"Name": "off;idle"}],
                  "APIs": [{"Name": "do_nothing", "EndState": ";"}]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Dual Mode Device", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("API 'do_nothing'")
                .contains("changes no mode");
    }

    @Test
    void signalApis_withSameStateRouteAreRejectedAsIndistinguishable() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Lamp",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [{"Name": "off"}, {"Name": "on"}],
                  "APIs": [
                    {"Name": "turn_on", "StartState": "off", "EndState": "on", "Signal": true},
                    {"Name": "activate", "StartState": "off", "EndState": "on", "Signal": true}
                  ]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Lamp", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("observable API 'turn_on' overlaps API 'activate'")
                .contains("cannot be distinguished as automation events");
    }

    @Test
    void apiSignalMustBeExplicit() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Lamp",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [
                    {"Name": "off", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "on", "Trust": "trusted", "Privacy": "public"}
                  ],
                  "APIs": [{"Name": "turn_on", "StartState": "off", "EndState": "on"}]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Lamp", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains(DeviceTemplateSchemaValidator.CANONICAL_SCHEMA_PATH)
                .contains("Signal");
    }

    @Test
    void apiStartStateMustBeExplicit() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Lamp",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [
                    {"Name": "off", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "on", "Trust": "trusted", "Privacy": "public"}
                  ],
                  "APIs": [{"Name": "turn_on", "EndState": "on", "Signal": true}]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Lamp", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains(DeviceTemplateSchemaValidator.CANONICAL_SCHEMA_PATH)
                .contains("StartState");
    }

    @Test
    void observableApiRouteCannotOverlapCommandOnlyApi() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Lamp",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [
                    {"Name": "off", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "on", "Trust": "trusted", "Privacy": "public"}
                  ],
                  "APIs": [
                    {"Name": "turn_on", "StartState": "off", "EndState": "on", "Signal": true},
                    {"Name": "restore", "StartState": "", "EndState": "on", "Signal": false}
                  ]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Lamp", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("observable API 'turn_on' overlaps API 'restore'")
                .contains("cannot be distinguished as automation events");
    }

    @Test
    void observableApiRouteCannotOverlapAutonomousTransition() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Lamp",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [
                    {"Name": "off", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "on", "Trust": "trusted", "Privacy": "public"}
                  ],
                  "APIs": [
                    {"Name": "turn_on", "StartState": "off", "EndState": "on", "Signal": true}
                  ],
                  "Transitions": [{
                    "Name": "automatic_on",
                    "StartState": "off",
                    "EndState": "on",
                    "Trigger": {"Attribute": "Power", "Relation": "=", "Value": "off"},
                    "Assignments": []
                  }]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Lamp", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("observable API 'turn_on' overlaps autonomous Transition 'automatic_on'")
                .contains("would expose that transition as the API event");
    }

    @Test
    void apiWithIdenticalConcreteStartAndEnd_isRejected() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Lamp",
                  "Modes": ["Power"],
                  "InitState": "on",
                  "WorkingStates": [{"Name": "on"}],
                  "APIs": [{"Name": "keep_on", "StartState": "on", "EndState": "on"}]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Lamp", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("identical concrete StartState and EndState")
                .contains("cannot change the formal model");
    }

    @Test
    void transitionSignal_isRejectedBecauseItHasNoUserReferenceSemantics() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Motion Sensor",
                  "InternalVariables": [{
                    "Name": "motion",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": true,
                    "Trust": "untrusted",
                    "Privacy": "public",
                    "Values": ["clear", "detected"]
                  }],
                  "Transitions": [{
                    "Name": "motion detected",
                    "Signal": true,
                    "Trigger": {"Attribute": "motion", "Relation": "=", "Value": "detected"},
                    "Assignments": [{"Attribute": "motion", "Value": "clear"}]
                  }]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Motion Sensor", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("backend/device-template-schema.json")
                .contains("Signal");
    }

    @Test
    void transitionAssignment_requiresTriggerAndDeclaredTarget() throws Exception {
        JsonNode missingTrigger = objectMapper.readTree("""
                {
                  "Name": "Counter",
                  "InternalVariables": [{
                    "Name": "counterValue",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "LowerBound": 0,
                    "UpperBound": 10
                  }],
                  "Transitions": [{
                    "Name": "reset",
                    "Assignments": [{"Attribute": "counterValue", "Value": "0"}]
                  }]
                }
                """);
        BadRequestException missingTriggerException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Counter", missingTrigger));
        org.assertj.core.api.Assertions.assertThat(missingTriggerException.getMessage())
                .contains("assigns variables but has no Trigger")
                .contains("never execute");

        JsonNode unknownTarget = objectMapper.readTree("""
                {
                  "Name": "Counter",
                  "InternalVariables": [{
                    "Name": "counterValue",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "LowerBound": 0,
                    "UpperBound": 10
                  }],
                  "Transitions": [{
                    "Name": "reset",
                    "Trigger": {"Attribute": "counterValue", "Relation": "=", "Value": "10"},
                    "Assignments": [{"Attribute": "missing", "Value": "0"}]
                  }]
                }
                """);
        BadRequestException unknownTargetException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Counter", unknownTarget));
        org.assertj.core.api.Assertions.assertThat(unknownTargetException.getMessage())
                .contains("assigns unknown variable 'missing'")
                .contains("InternalVariables or EnvironmentDomains");
    }

    @Test
    void transitionAssignment_valueMustFitDeclaredDomain() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Counter",
                  "InternalVariables": [{
                    "Name": "counterValue",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "LowerBound": 0,
                    "UpperBound": 10
                  }],
                  "Transitions": [{
                    "Name": "overflow",
                    "Trigger": {"Attribute": "counterValue", "Relation": "=", "Value": "10"},
                    "Assignments": [{"Attribute": "counterValue", "Value": "11"}]
                  }]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Counter", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("assigns 11 to 'counterValue'")
                .contains("outside its range 0..10");
    }

    @Test
    void triggeredTransitionAssignment_isRepresentable() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Counter",
                  "InternalVariables": [{
                    "Name": "counterValue",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "LowerBound": 0,
                    "UpperBound": 10
                  }],
                  "Transitions": [{
                    "Name": "reset",
                    "Trigger": {"Attribute": "counterValue", "Relation": "=", "Value": "10"},
                    "Assignments": [{"Attribute": "counterValue", "Value": "0"}]
                  }]
                }
                """);

        assertDoesNotThrow(() -> validator.validateRawManifest("Counter", manifest));
    }

    @Test
    void transitionWithMultipleEffects_isRejectedInsteadOfPartiallyApplying() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Controller",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [
                    {"Name": "off", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "on", "Trust": "trusted", "Privacy": "public"}
                  ],
                  "InternalVariables": [{
                    "Name": "level",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "LowerBound": 0,
                    "UpperBound": 10
                  }],
                  "Transitions": [{
                    "Name": "activate",
                    "StartState": "off",
                    "EndState": "on",
                    "Trigger": {"Attribute": "level", "Relation": "=", "Value": "10"},
                    "Assignments": [{"Attribute": "level", "Value": "0"}]
                  }]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Controller", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("Transition 'activate'")
                .contains("cannot preserve those effects as one atomic action")
                .contains("single-effect transitions");
    }

    @Test
    void multiModeTransitionChangingTwoModes_isRejectedAsNonAtomic() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Dual Controller",
                  "Modes": ["Power", "Profile"],
                  "InitState": "off;eco",
                  "WorkingStates": [
                    {"Name": "off;eco", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "on;boost", "Trust": "trusted", "Privacy": "public"}
                  ],
                  "Transitions": [{
                    "Name": "activate boost",
                    "StartState": "off;eco",
                    "EndState": "on;boost",
                    "Trigger": {"Attribute": "Power", "Relation": "=", "Value": "off"}
                  }]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Dual Controller", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("Transition 'activate boost'")
                .contains("2 state/variable effects")
                .contains("atomic action");
    }

    @Test
    void statelessTransitionCannotPretendToChangeState() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Counter",
                  "InternalVariables": [{
                    "Name": "counterValue",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "LowerBound": 0,
                    "UpperBound": 10
                  }],
                  "Transitions": [{
                    "Name": "phantom state",
                    "EndState": "active",
                    "Trigger": {"Attribute": "counterValue", "Relation": "=", "Value": "10"}
                  }]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Counter", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("has no Modes")
                .contains("Stateless transitions")
                .contains("variable Assignment");
    }

    @Test
    void transitionTriggerMustUseAValueAndRelationFromItsDomain() throws Exception {
        JsonNode invalidValue = objectMapper.readTree("""
                {
                  "Name": "Switch",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [
                    {"Name": "off", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "on", "Trust": "trusted", "Privacy": "public"}
                  ],
                  "Transitions": [{
                    "Name": "invalid trigger",
                    "EndState": "on",
                    "Trigger": {"Attribute": "Power", "Relation": "=", "Value": "standby"}
                  }]
                }
                """);
        BadRequestException invalidValueException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Switch", invalidValue));
        org.assertj.core.api.Assertions.assertThat(invalidValueException.getMessage())
                .contains("unknown value 'standby'")
                .contains("Allowed values");

        JsonNode invalidRelation = objectMapper.readTree("""
                {
                  "Name": "Switch",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [
                    {"Name": "off", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "on", "Trust": "trusted", "Privacy": "public"}
                  ],
                  "Transitions": [{
                    "Name": "invalid relation",
                    "EndState": "on",
                    "Trigger": {"Attribute": "Power", "Relation": ">", "Value": "off"}
                  }]
                }
                """);
        BadRequestException invalidRelationException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Switch", invalidRelation));
        org.assertj.core.api.Assertions.assertThat(invalidRelationException.getMessage())
                .contains("ordering relation")
                .contains("Use = or !=");
    }

    @Test
    void workingStateDynamicsMustTargetWritableVariableWithDomainAppropriateEffect() throws Exception {
        JsonNode unknownTarget = objectMapper.readTree("""
                {
                  "Name": "Heater",
                  "Modes": ["Power"],
                  "InitState": "on",
                  "WorkingStates": [{
                    "Name": "on",
                    "Trust": "trusted",
                    "Privacy": "public",
                    "Dynamics": [{"VariableName": "temperature", "ChangeRate": "1"}]
                  }]
                }
                """);
        BadRequestException unknownTargetException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Heater", unknownTarget));
        org.assertj.core.api.Assertions.assertThat(unknownTargetException.getMessage())
                .contains("unknown or non-writable variable 'temperature'")
                .contains("ImpactedVariables");

        JsonNode wrongEffect = objectMapper.readTree("""
                {
                  "Name": "Door",
                  "Modes": ["Position"],
                  "InitState": "closed",
                  "WorkingStates": [{
                    "Name": "closed",
                    "Trust": "trusted",
                    "Privacy": "public",
                    "Dynamics": [{"VariableName": "contact", "ChangeRate": "1"}]
                  }],
                  "InternalVariables": [{
                    "Name": "contact",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "Values": ["closed", "open"]
                  }]
                }
                """);
        BadRequestException wrongEffectException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Door", wrongEffect));
        org.assertj.core.api.Assertions.assertThat(wrongEffectException.getMessage())
                .contains("must use Value for enum/boolean Dynamics target 'contact'")
                .contains("no discrete-domain meaning");
    }

    @Test
    void workingStateExplicitBooleanEnumDynamicsIsAcceptedAndOutOfDomainValueIsRejected() throws Exception {
        JsonNode valid = objectMapper.readTree("""
                {
                  "Name": "Presence Latch",
                  "Modes": ["Power"],
                  "InitState": "on",
                  "WorkingStates": [{
                    "Name": "on",
                    "Trust": "trusted",
                    "Privacy": "public",
                    "Dynamics": [{"VariableName": "occupied", "Value": "TRUE"}]
                  }],
                  "InternalVariables": [{
                    "Name": "occupied",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "Values": ["TRUE", "FALSE"]
                  }]
                }
                """);
        assertDoesNotThrow(() -> validator.validateRawManifest("Presence Latch", valid));

        JsonNode invalid = valid.deepCopy();
        ((com.fasterxml.jackson.databind.node.ObjectNode) invalid.path("WorkingStates").get(0)
                .path("Dynamics").get(0)).put("Value", "maybe");
        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Presence Latch", invalid));
        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("Dynamics target 'occupied'")
                .contains("outside its enum domain")
                .contains("TRUE")
                .contains("FALSE");
    }

    @Test
    void variableDomainsRejectDescendingRangesAndNormalizedEnumDuplicates() throws Exception {
        JsonNode descending = objectMapper.readTree("""
                {
                  "Name": "Meter",
                  "InternalVariables": [{
                    "Name": "level",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "LowerBound": 10,
                    "UpperBound": 0
                  }]
                }
                """);
        BadRequestException descendingException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Meter", descending));
        org.assertj.core.api.Assertions.assertThat(descendingException.getMessage())
                .contains("LowerBound 10 greater than UpperBound 0");

        JsonNode duplicateEnum = objectMapper.readTree("""
                {
                  "Name": "Status",
                  "InternalVariables": [{
                    "Name": "state",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "Values": ["not ready", "notready"]
                  }]
                }
                """);
        BadRequestException duplicateException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Status", duplicateEnum));
        org.assertj.core.api.Assertions.assertThat(duplicateException.getMessage())
                .contains("duplicate enum value 'notready'")
                .contains("spaces are removed");
    }

    @Test
    void naturalChangeRateRequiresNumericDomainAndSupportedIntegerRange() throws Exception {
        JsonNode enumRate = objectMapper.readTree("""
                {
                  "Name": "Status",
                  "InternalVariables": [{
                    "Name": "status",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "Values": ["ready", "busy"],
                    "NaturalChangeRate": "1"
                  }]
                }
                """);
        BadRequestException enumException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Status", enumRate));
        org.assertj.core.api.Assertions.assertThat(enumException.getMessage())
                .contains("only numeric ranges can change by a rate");

        JsonNode overflow = objectMapper.readTree("""
                {
                  "Name": "Meter",
                  "InternalVariables": [{
                    "Name": "level",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": false,
                    "Trust": "trusted",
                    "Privacy": "public",
                    "LowerBound": 0,
                    "UpperBound": 100,
                    "NaturalChangeRate": "999999999999"
                  }]
                }
                """);
        BadRequestException overflowException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Meter", overflow));
        org.assertj.core.api.Assertions.assertThat(overflowException.getMessage())
                .contains("outside the supported integer format")
                .contains("999999999999");
    }

    @Test
    void sharedEnvironmentVariable_requiresExplicitTrustAndPrivacy() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Temperature Sensor",
                  "InternalVariables": [{
                    "Name": "temperature",
                    "IsInside": false,
                    "FalsifiableWhenCompromised": true,
                    "LowerBound": 0,
                    "UpperBound": 100,
                    "Trust": "untrusted"
                  }]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Temperature Sensor", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage()).contains("Privacy");
    }

    @Test
    void impactOnlyEnvironmentDomain_requiresExplicitTrustAndPrivacy() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Light",
                  "EnvironmentDomains": [{
                    "Name": "illuminance",
                    "LowerBound": 0,
                    "UpperBound": 100,
                    "Privacy": "public"
                  }],
                  "ImpactedVariables": ["illuminance"]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Light", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage()).contains("Trust");
    }

    @Test
    void everyModeledSourceAndContent_requiresExplicitSecurityLabels() throws Exception {
        JsonNode missingStateLabels = objectMapper.readTree("""
                {
                  "Name": "State Sensor",
                  "Modes": ["Detection"],
                  "InitState": "clear",
                  "WorkingStates": [{"Name": "clear"}]
                }
                """);
        JsonNode missingLocalVariableLabels = objectMapper.readTree("""
                {
                  "Name": "Local Sensor",
                  "InternalVariables": [{
                    "Name": "reading",
                    "IsInside": true,
                    "FalsifiableWhenCompromised": true,
                    "LowerBound": 0,
                    "UpperBound": 100
                  }]
                }
                """);
        JsonNode missingContentPrivacy = objectMapper.readTree("""
                {
                  "Name": "Camera",
                  "Contents": [{"Name": "photo"}]
                }
                """);

        BadRequestException stateException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("State Sensor", missingStateLabels));
        BadRequestException variableException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Local Sensor", missingLocalVariableLabels));
        BadRequestException contentException = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Camera", missingContentPrivacy));

        org.assertj.core.api.Assertions.assertThat(stateException.getMessage())
                .contains("WorkingStates[0]").contains("Trust").contains("Privacy");
        org.assertj.core.api.Assertions.assertThat(variableException.getMessage())
                .contains("InternalVariables[0]").contains("Trust").contains("Privacy");
        org.assertj.core.api.Assertions.assertThat(contentException.getMessage())
                .contains("Contents[0]").contains("Privacy");
    }

    @Test
    void rawWorkingStateInvariant_isRejectedInsteadOfPretendingToConstrainTheModel() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Lamp",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [{
                    "Name": "off",
                    "Trust": "trusted",
                    "Privacy": "public",
                    "Invariant": "level < 50"
                  }]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Lamp", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("backend/device-template-schema.json")
                .contains("Invariant");
    }

    @Test
    void multiModeWorkingState_requiresOneConcreteValuePerMode() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Washer",
                  "Modes": ["Program", "MachineState"],
                  "InitState": "regular;idle",
                  "WorkingStates": [
                    {"Name": "regular;idle", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "running", "Trust": "trusted", "Privacy": "public"}
                  ]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Washer", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("WorkingState 'running'")
                .contains("each mode");
    }

    @Test
    void reusedModeState_rejectsConflictingTrustOrPrivacyLabels() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Home Profile",
                  "Modes": ["Occupancy", "MachineState"],
                  "InitState": "home;idle",
                  "WorkingStates": [
                    {"Name": "home;idle", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "away;idle", "Trust": "untrusted", "Privacy": "public"}
                  ]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class, () ->
                validator.validateRawManifest("Home Profile", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("home;idle")
                .contains("away;idle")
                .contains("MachineState='idle'")
                .contains("cannot be represented losslessly");
    }

    @Test
    void apiAssignmentsFieldIsRejectedEvenWhenEmpty() throws Exception {
        JsonNode manifest = objectMapper.readTree("""
                {
                  "Name": "Lamp",
                  "Modes": ["Power"],
                  "InitState": "off",
                  "WorkingStates": [
                    {"Name": "off", "Trust": "trusted", "Privacy": "public"},
                    {"Name": "on", "Trust": "trusted", "Privacy": "public"}
                  ],
                  "APIs": [{
                    "Name": "turn_on",
                    "StartState": "off",
                    "EndState": "on",
                    "Signal": true,
                    "Assignments": []
                  }]
                }
                """);

        BadRequestException exception = assertThrows(BadRequestException.class,
                () -> validator.validateRawManifest("Lamp", manifest));

        org.assertj.core.api.Assertions.assertThat(exception.getMessage())
                .contains("unsupported Assignments field")
                .contains("triggered Transition");
    }

    private void assertVariableTrust(String templateName, String variableName, String expectedTrust)
            throws Exception {
        JsonNode manifest = objectMapper.readTree(
                Path.of("src/main/resources/deviceTemplate", templateName + ".json").toFile());
        for (JsonNode variable : manifest.path("InternalVariables")) {
            if (variableName.equals(variable.path("Name").asText())) {
                assertEquals(expectedTrust, variable.path("Trust").asText(),
                        () -> templateName + "." + variableName
                                + " should use MEDIC origin semantics");
                return;
            }
        }
        throw new AssertionError("Missing variable " + templateName + "." + variableName);
    }
}
