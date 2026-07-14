package cn.edu.nju.Iot_Verify.component.nusmv.generator.data;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.*;

class DeviceReferenceResolverTest {

    private DeviceSmvData device(String varName, String templateName) {
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName(varName);
        smv.setTemplateName(templateName);
        return smv;
    }

    @Test
    void resolve_usesExactReferenceOnly() {
        DeviceSmvData primary = device("primary_var", "PrimaryTemplate");
        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("primaryId", primary);

        assertSame(primary, DeviceReferenceResolver.resolve("primaryId", map));
    }

    @Test
    void resolve_doesNotFallBackToDisplayLabel() {
        DeviceSmvData secondary = device("LivingRoomAC", "AC");
        Map<String, DeviceSmvData> map = Map.of("LivingRoomAC", secondary);

        assertNull(DeviceReferenceResolver.resolve("ac_1", map));
    }

    @Test
    void resolve_rejectsNonCanonicalDigitLeadingReference() {
        DeviceSmvData lamp = device("_1lamp", "Lamp");
        Map<String, DeviceSmvData> map = Map.of("_1lamp", lamp);

        assertNull(DeviceReferenceResolver.resolve("1Lamp", map));
    }

    @Test
    void resolvableReference_returnsCanonicalInputReferenceOnly() {
        DeviceSmvData lamp = device("_1lamp", "Lamp");
        Map<String, DeviceSmvData> map = Map.of("_1lamp", lamp);

        assertEquals("_1lamp", DeviceReferenceResolver.resolvableReference("_1lamp", map));
        assertNull(DeviceReferenceResolver.resolvableReference("1Lamp", map));
    }

    @Test
    void canonicalReference_returnsResolvedCanonicalReference() {
        DeviceSmvData currentBoardLamp = device("_1lamp", "Lamp");
        Map<String, DeviceSmvData> map = Map.of("_1lamp", currentBoardLamp);

        assertEquals("_1lamp", DeviceReferenceResolver.canonicalReference("_1lamp", map));
        assertNull(DeviceReferenceResolver.canonicalReference("1Lamp", map));
    }

    @Test
    void unresolvedReferences_returnNull() {
        assertNull(DeviceReferenceResolver.resolve("missing", Map.of()));
        assertNull(DeviceReferenceResolver.resolvableReference(" missing ", Map.of()));
        assertNull(DeviceReferenceResolver.canonicalReference(null, Map.of()));
    }

    @Test
    void resolve_doesNotUseTemplateFallback() {
        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("ac_1", device("ac_1", "AC"));
        map.put("ac_2", device("ac_2", "AC"));

        assertNull(DeviceReferenceResolver.resolve("AC", map));
    }

    @Test
    void resolvableReference_doesNotUseTemplateFallback() {
        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("ac_1", device("ac_1", "AC"));
        map.put("ac_2", device("ac_2", "AC"));

        assertNull(DeviceReferenceResolver.resolvableReference("AC", map));
    }
}
