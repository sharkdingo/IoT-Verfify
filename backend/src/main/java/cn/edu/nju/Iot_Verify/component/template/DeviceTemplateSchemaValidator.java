package cn.edu.nju.Iot_Verify.component.template;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.exception.BadRequestException;
import cn.edu.nju.Iot_Verify.exception.InternalServerException;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import com.networknt.schema.JsonSchema;
import com.networknt.schema.JsonSchemaFactory;
import com.networknt.schema.SpecVersion;
import com.networknt.schema.ValidationMessage;
import lombok.RequiredArgsConstructor;
import org.springframework.beans.factory.annotation.Value;
import org.springframework.core.io.ClassPathResource;
import org.springframework.core.io.FileSystemResource;
import org.springframework.core.io.Resource;
import org.springframework.stereotype.Component;

import java.io.IOException;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

@Component
@RequiredArgsConstructor
public class DeviceTemplateSchemaValidator {

    public static final String CANONICAL_SCHEMA_PATH = "backend/device-template-schema.json";

    private final ObjectMapper objectMapper;

    @Value("${device-template.schema-path:device-template-schema.json}")
    private String schemaPath = "device-template-schema.json";

    private volatile JsonSchema schema;
    private volatile ObjectMapper nonNullObjectMapper;

    public void validateRawManifest(String templateName, JsonNode manifestNode) {
        if (manifestNode == null || !manifestNode.isObject()) {
            throw new BadRequestException("Template manifest is required and must be a JSON object.");
        }
        validateNode(templateName, manifestNode);
    }

    public void validateManifest(String templateName, DeviceManifest manifest) {
        if (manifest == null) {
            throw new BadRequestException("Template manifest is required.");
        }
        validateNode(templateName, toSchemaNode(manifest));
    }

    private void validateNode(String templateName, JsonNode manifestNode) {
        Set<ValidationMessage> messages = getSchema().validate(manifestNode);
        if (messages.isEmpty()) {
            return;
        }
        String details = messages.stream()
                .limit(5)
                .map(ValidationMessage::getMessage)
                .collect(Collectors.joining("; "));
        if (messages.size() > 5) {
            details += "; ... " + (messages.size() - 5) + " more";
        }
        String name = templateName == null || templateName.isBlank() ? "<unnamed>" : templateName;
        throw new BadRequestException("Template '" + name + "' does not match "
                + CANONICAL_SCHEMA_PATH + ": " + details);
    }

    private JsonSchema getSchema() {
        JsonSchema current = schema;
        if (current != null) {
            return current;
        }
        synchronized (this) {
            if (schema == null) {
                schema = loadSchema();
            }
            return schema;
        }
    }

    private JsonSchema loadSchema() {
        JsonNode schemaNode = readSchemaNode();
        JsonSchemaFactory factory = JsonSchemaFactory.getInstance(SpecVersion.VersionFlag.V202012);
        return factory.getSchema(schemaNode);
    }

    private JsonNode toSchemaNode(DeviceManifest manifest) {
        return getNonNullObjectMapper().valueToTree(manifest);
    }

    private ObjectMapper getNonNullObjectMapper() {
        ObjectMapper current = nonNullObjectMapper;
        if (current != null) {
            return current;
        }
        synchronized (this) {
            if (nonNullObjectMapper == null) {
                nonNullObjectMapper = objectMapper.copy()
                        .setSerializationInclusion(JsonInclude.Include.NON_NULL);
            }
            return nonNullObjectMapper;
        }
    }

    private JsonNode readSchemaNode() {
        List<Resource> candidates = List.of(
                new FileSystemResource(schemaPath),
                new FileSystemResource(CANONICAL_SCHEMA_PATH),
                new ClassPathResource("device-template-schema.json")
        );
        for (Resource resource : candidates) {
            try {
                if (resource.exists() && resource.isReadable()) {
                    try (var input = resource.getInputStream()) {
                        return objectMapper.readTree(input);
                    }
                }
            } catch (IOException e) {
                throw new InternalServerException("Failed to read device template schema from "
                        + resource.getDescription(), e);
            }
        }
        throw new InternalServerException("Device template schema not found. Expected "
                + CANONICAL_SCHEMA_PATH + " or classpath:device-template-schema.json.");
    }
}
