package cn.edu.nju.Iot_Verify.component.nusmv.generator.data;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

class DeviceSmvDataFactorySanitizationTest {

    @Test
    void sanitizeSmvToken_reservedWords_caseInsensitiveAndWeakUntilEscaped() {
        assertTrue(DeviceSmvDataFactory.sanitizeSmvToken("CASE").startsWith("_"));
        assertTrue(DeviceSmvDataFactory.sanitizeSmvToken("NEXT").startsWith("_"));
        assertTrue(DeviceSmvDataFactory.sanitizeSmvToken("BOOLEAN").startsWith("_"));
        assertTrue(DeviceSmvDataFactory.sanitizeSmvToken("case").startsWith("_"));
        assertTrue(DeviceSmvDataFactory.sanitizeSmvToken("next").startsWith("_"));

        // NuSMV weak-until operator token should be treated as reserved.
        assertTrue(DeviceSmvDataFactory.sanitizeSmvToken("W").startsWith("_"));
        assertTrue(DeviceSmvDataFactory.sanitizeSmvToken("w").startsWith("_"));

        assertFalse(DeviceSmvDataFactory.sanitizeSmvToken("sensor_temp").startsWith("_"));
    }

    @Test
    void toVarName_digitPrefix_isEscaped() {
        assertEquals("_123abc", DeviceSmvDataFactory.toVarName("123abc"));
        assertEquals("_999", DeviceSmvDataFactory.toVarName("999"));
        assertEquals("abc123", DeviceSmvDataFactory.toVarName("abc123"));
    }
}
