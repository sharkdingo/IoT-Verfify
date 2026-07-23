package cn.edu.nju.Iot_Verify.dto.device;

import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

class DeviceRuntimeSerializationTest {

    private final ObjectMapper objectMapper = new ObjectMapper();

    @Test
    void inheritedVariableTrustIsOmittedWhileExplicitTrustIsPreserved() {
        JsonNode inherited = objectMapper.valueToTree(
                new VariableStateDto("temperature", "20", null));
        JsonNode overridden = objectMapper.valueToTree(
                new VariableStateDto("temperature", "20", "untrusted"));

        assertFalse(inherited.has("trust"));
        assertEquals("untrusted", overridden.path("trust").asText());
    }
}
