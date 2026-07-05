package cn.edu.nju.Iot_Verify.component.template;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
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
    void dtoManifestValidation_treatsNullOptionalNestedFieldsAsOmitted() {
        DeviceManifest manifest = new DeviceManifest();
        manifest.setName("Lamp");
        manifest.setModes(List.of("LampState"));
        manifest.setInitState("off");

        DeviceManifest.WorkingState off = new DeviceManifest.WorkingState();
        off.setName("off");
        DeviceManifest.WorkingState on = new DeviceManifest.WorkingState();
        on.setName("on");
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
}
