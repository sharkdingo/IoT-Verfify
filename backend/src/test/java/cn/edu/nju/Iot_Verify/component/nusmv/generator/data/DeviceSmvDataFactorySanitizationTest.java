package cn.edu.nju.Iot_Verify.component.nusmv.generator.data;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.CsvSource;

import java.lang.reflect.Method;

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

    // ── computeIdentifiers tests (reflection into private method) ──

    /**
     * Invoke the private computeIdentifiers(DeviceSmvData, String) via reflection.
     * The factory's final fields (objectMapper, deviceTemplateService, modelValidator)
     * are not used by computeIdentifiers, so passing nulls is safe.
     */
    private DeviceSmvData callComputeIdentifiers(String templateName, String rawVarName) throws Exception {
        DeviceSmvData smv = new DeviceSmvData();
        smv.setTemplateName(templateName);
        DeviceSmvDataFactory factory = new DeviceSmvDataFactory(null, null, null);
        Method m = DeviceSmvDataFactory.class.getDeclaredMethod("computeIdentifiers", DeviceSmvData.class, String.class);
        m.setAccessible(true);
        m.invoke(factory, smv, rawVarName);
        return smv;
    }

    @ParameterizedTest
    @CsvSource({
            "123Lamp,   myvar,   _123Lamp",     // digit-prefixed templateName -> base gets _ prefix
            "9,         dev1,    _9",            // single digit templateName
            "Lamp,      myvar,   Lamp",          // normal templateName — no prefix
            "MODULE,    myvar,   _MODULE",       // reserved-word templateName -> base gets _ prefix
            "case,      myvar,   _case",         // lowercase reserved word
    })
    void computeIdentifiers_base_digitPrefixAndReservedWord(String templateName, String rawVarName,
                                                             String expectedBasePrefix) throws Exception {
        DeviceSmvData smv = callComputeIdentifiers(templateName, rawVarName);
        String moduleName = smv.getModuleName();
        assertTrue(moduleName.startsWith(expectedBasePrefix + "_"),
                "moduleName '" + moduleName + "' should start with '" + expectedBasePrefix + "_'");
    }

    @Test
    void computeIdentifiers_varName_digitPrefixGuard() throws Exception {
        DeviceSmvData smv = callComputeIdentifiers("Lamp", "3sensor");
        assertEquals("_3sensor", smv.getVarName());
        assertFalse(Character.isDigit(smv.getModuleName().charAt(0)),
                "moduleName should not start with a digit: " + smv.getModuleName());
    }

    @Test
    void computeIdentifiers_allEdgeCases() throws Exception {
        // null rawVarName -> fallback to "device_0"
        DeviceSmvData smv1 = callComputeIdentifiers("Lamp", null);
        assertEquals("device_0", smv1.getVarName());

        // empty templateName (after stripping non-alphanumeric) -> fallback to "Device"
        DeviceSmvData smv2 = callComputeIdentifiers("---", "myvar");
        assertTrue(smv2.getModuleName().startsWith("Device_"),
                "moduleName should start with 'Device_': " + smv2.getModuleName());

        // all-underscore rawVarName -> fallback to "device_0"
        DeviceSmvData smv3 = callComputeIdentifiers("Lamp", "___");
        assertEquals("device_0", smv3.getVarName());
    }
}
