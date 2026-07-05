package cn.edu.nju.Iot_Verify.component.nusmv.generator.data;

import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
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
    void resolve_prefersPrimaryExactMatchOverSecondary() {
        DeviceSmvData primary = device("primary_var", "PrimaryTemplate");
        DeviceSmvData secondary = device("secondary_var", "SecondaryTemplate");
        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("primaryLabel", primary);
        map.put("secondaryLabel", secondary);

        assertSame(primary, DeviceReferenceResolver.resolve("primaryLabel", "secondaryLabel", map));
    }

    @Test
    void resolve_fallsBackToSecondaryWhenPrimaryDoesNotResolve() {
        DeviceSmvData secondary = device("LivingRoomAC", "AC");
        Map<String, DeviceSmvData> map = Map.of("LivingRoomAC", secondary);

        assertSame(secondary, DeviceReferenceResolver.resolve("ac_1", "LivingRoomAC", map));
    }

    @Test
    void resolve_usesNormalizedDigitLeadingReference() {
        DeviceSmvData lamp = device("d_1Lamp", "Lamp");
        Map<String, DeviceSmvData> map = Map.of("d_1Lamp", lamp);

        assertSame(lamp, DeviceReferenceResolver.resolve("1Lamp", null, map));
    }

    @Test
    void resolvableReference_returnsResolvableInputReferenceNotSmvVarName() {
        DeviceSmvData lamp = device("d_1lamp", "Lamp");
        Map<String, DeviceSmvData> map = Map.of("d_1Lamp", lamp);

        assertEquals("d_1Lamp", DeviceReferenceResolver.resolvableReference("1Lamp", null, map));
    }

    @Test
    void canonicalReference_normalizesResolvedReferenceForSemanticComparison() {
        DeviceSmvData currentBoardLamp = device("_1lamp", "Lamp");
        Map<String, DeviceSmvData> map = Map.of("1Lamp", currentBoardLamp);

        assertEquals("d_1Lamp", DeviceReferenceResolver.canonicalReference("1Lamp", null, map));
    }

    @Test
    void unresolvedReferences_returnFirstNonBlankFallbacks() {
        assertNull(DeviceReferenceResolver.resolve("missing", null, Map.of()));
        assertEquals("missing", DeviceReferenceResolver.resolvableReference(" missing ", null, Map.of()));
        assertEquals("d_1Lamp", DeviceReferenceResolver.canonicalReference(null, "1Lamp", Map.of()));
    }

    @Test
    void resolve_throwsAmbiguousTemplateFallbackWhenNoExactOrSecondaryMatch() {
        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("ac_1", device("ac_1", "AC"));
        map.put("ac_2", device("ac_2", "AC"));

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> DeviceReferenceResolver.resolve("AC", null, map));

        assertEquals(SmvGenerationException.ErrorCategories.AMBIGUOUS_DEVICE_REFERENCE,
                ex.getErrorCategory());
    }

    @Test
    void resolvableReference_throwsAmbiguousTemplateFallback() {
        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("ac_1", device("ac_1", "AC"));
        map.put("ac_2", device("ac_2", "AC"));

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> DeviceReferenceResolver.resolvableReference("AC", null, map));

        assertEquals(SmvGenerationException.ErrorCategories.AMBIGUOUS_DEVICE_REFERENCE,
                ex.getErrorCategory());
    }
}
