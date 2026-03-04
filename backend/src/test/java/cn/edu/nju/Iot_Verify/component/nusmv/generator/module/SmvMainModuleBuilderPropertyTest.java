package cn.edu.nju.Iot_Verify.component.nusmv.generator.module;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.PropertyDimension;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.util.*;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Unit tests for trust/privacy property condition logic in SmvMainModuleBuilder.
 * Covers parseStateValueSet, collectStatePropertyPartsIncluding/Excluding,
 * resolveAttributeAsMode, and the fail-closed behavior of appendRulePropertyConditions.
 */
class SmvMainModuleBuilderPropertyTest {

    private SmvMainModuleBuilder builder;

    @BeforeEach
    void setUp() {
        builder = new SmvMainModuleBuilder();
    }

    // ── Test data builders ──

    private static DeviceSmvData buildMultiModeDevice() {
        DeviceSmvData d = new DeviceSmvData();
        d.setVarName("aircon_1");
        d.setModes(List.of("cool", "heat"));
        d.setModeStates(new LinkedHashMap<>(Map.of(
                "cool", List.of("on", "off", "standby"),
                "heat", List.of("on", "off", "standby"))));
        d.setStates(List.of("on", "off", "standby"));
        return d;
    }

    private static DeviceSmvData buildSingleModeDevice() {
        DeviceSmvData d = new DeviceSmvData();
        d.setVarName("light_1");
        d.setModes(List.of("power"));
        d.setModeStates(new LinkedHashMap<>(Map.of(
                "power", List.of("on", "off", "dim"))));
        d.setStates(List.of("on", "off", "dim"));
        return d;
    }

    private static DeviceSmvData buildNoModeDevice() {
        DeviceSmvData d = new DeviceSmvData();
        d.setVarName("sensor_1");
        d.setModes(List.of());
        d.setModeStates(new LinkedHashMap<>());
        d.setStates(List.of("active", "idle"));
        return d;
    }

    // ── Reflection helpers ──

    private Set<String> invokeParseStateValueSet(String raw, DeviceSmvData condSmv) throws Exception {
        Method m = SmvMainModuleBuilder.class.getDeclaredMethod("parseStateValueSet", String.class, DeviceSmvData.class);
        m.setAccessible(true);
        @SuppressWarnings("unchecked")
        Set<String> result = (Set<String>) m.invoke(builder, raw, condSmv);
        return result;
    }

    private String invokeCollectIncluding(DeviceSmvData condSmv, String varName,
                                          PropertyDimension dim, Set<String> values,
                                          String targetMode) throws Exception {
        Method m = SmvMainModuleBuilder.class.getDeclaredMethod(
                "collectStatePropertyPartsIncluding",
                DeviceSmvData.class, String.class, PropertyDimension.class, Set.class, String.class);
        m.setAccessible(true);
        return (String) m.invoke(builder, condSmv, varName, dim, values, targetMode);
    }

    private String invokeCollectExcluding(DeviceSmvData condSmv, String varName,
                                          PropertyDimension dim, Set<String> values,
                                          String targetMode) throws Exception {
        Method m = SmvMainModuleBuilder.class.getDeclaredMethod(
                "collectStatePropertyPartsExcluding",
                DeviceSmvData.class, String.class, PropertyDimension.class, Set.class, String.class);
        m.setAccessible(true);
        return (String) m.invoke(builder, condSmv, varName, dim, values, targetMode);
    }

    private static String invokeResolveAttributeAsMode(DeviceSmvData condSmv,
                                                       RuleDto.Condition condition) throws Exception {
        Method m = SmvMainModuleBuilder.class.getDeclaredMethod(
                "resolveAttributeAsMode", DeviceSmvData.class, RuleDto.Condition.class);
        m.setAccessible(true);
        return (String) m.invoke(null, condSmv, condition);
    }

    // ── parseStateValueSet ──

    @Nested
    @DisplayName("parseStateValueSet")
    class ParseStateValueSetTests {

        @Test
        @DisplayName("single-mode: splits by comma, semicolon, and pipe")
        void singleMode_allSeparators() throws Exception {
            Set<String> result = invokeParseStateValueSet("A,B;C|D", buildSingleModeDevice());
            assertEquals(Set.of("A", "B", "C", "D"), result);
        }

        @Test
        @DisplayName("multi-mode: preserves semicolon as tuple separator, splits by comma and pipe")
        void multiMode_preservesSemicolon() throws Exception {
            Set<String> result = invokeParseStateValueSet("cool;on,heat;off", buildMultiModeDevice());
            assertEquals(Set.of("cool;on", "heat;off"), result);
        }

        @Test
        @DisplayName("multi-mode: pipe separates values")
        void multiMode_pipeSeparator() throws Exception {
            Set<String> result = invokeParseStateValueSet("on|off", buildMultiModeDevice());
            assertEquals(Set.of("on", "off"), result);
        }

        @Test
        @DisplayName("strips brackets")
        void stripsBrackets() throws Exception {
            Set<String> result = invokeParseStateValueSet("[A,B,C]", buildSingleModeDevice());
            assertEquals(Set.of("A", "B", "C"), result);
        }

        @Test
        @DisplayName("strips spaces")
        void stripsSpaces() throws Exception {
            Set<String> result = invokeParseStateValueSet(" A , B , C ", buildSingleModeDevice());
            assertEquals(Set.of("A", "B", "C"), result);
        }
    }

    // ── resolveAttributeAsMode ──

    @Nested
    @DisplayName("resolveAttributeAsMode")
    class ResolveAttributeAsModeTests {

        @Test
        @DisplayName("returns mode name when attribute matches a mode")
        void attributeIsMode() throws Exception {
            RuleDto.Condition cond = RuleDto.Condition.builder()
                    .deviceName("aircon").attribute("cool").relation("!=").value("on").build();
            assertEquals("cool", invokeResolveAttributeAsMode(buildMultiModeDevice(), cond));
        }

        @Test
        @DisplayName("returns null when attribute does not match any mode")
        void attributeNotMode() throws Exception {
            RuleDto.Condition cond = RuleDto.Condition.builder()
                    .deviceName("aircon").attribute("state").relation("!=").value("on").build();
            assertNull(invokeResolveAttributeAsMode(buildMultiModeDevice(), cond));
        }

        @Test
        @DisplayName("returns null for no-mode device")
        void noModeDevice_returnsNull() throws Exception {
            RuleDto.Condition cond = RuleDto.Condition.builder()
                    .deviceName("sensor").attribute("active").relation("=").value("true").build();
            assertNull(invokeResolveAttributeAsMode(buildNoModeDevice(), cond));
        }
    }

    // ── collectStatePropertyPartsIncluding ──

    @Nested
    @DisplayName("collectStatePropertyPartsIncluding")
    class IncludingTests {

        @Test
        @DisplayName("no targetMode: simple value finds first matching mode")
        void noTargetMode_simpleValue() throws Exception {
            // "on" exists in both cool and heat; should pick first mode (cool)
            String result = invokeCollectIncluding(buildMultiModeDevice(), "aircon_1",
                    PropertyDimension.TRUST, Set.of("on"), null);
            assertEquals("aircon_1.trust_cool_on=trusted", result);
        }

        @Test
        @DisplayName("targetMode: scopes to specified mode even when shared state")
        void targetMode_scopesToMode() throws Exception {
            // with targetMode="heat", should pick heat, not cool
            String result = invokeCollectIncluding(buildMultiModeDevice(), "aircon_1",
                    PropertyDimension.TRUST, Set.of("on"), "heat");
            assertEquals("aircon_1.trust_heat_on=trusted", result);
        }

        @Test
        @DisplayName("no targetMode: tuple value resolved per-mode")
        void noTargetMode_tupleValue() throws Exception {
            String result = invokeCollectIncluding(buildMultiModeDevice(), "aircon_1",
                    PropertyDimension.TRUST, Set.of("on;off"), null);
            // Tuple "on;off" → cool=on, heat=off
            assertNotNull(result);
            assertTrue(result.contains("trust_cool_on=trusted"));
            assertTrue(result.contains("trust_heat_off=trusted"));
        }

        @Test
        @DisplayName("multiple values joined with &")
        void multipleValues() throws Exception {
            String result = invokeCollectIncluding(buildMultiModeDevice(), "aircon_1",
                    PropertyDimension.TRUST, new LinkedHashSet<>(List.of("on", "off")), "cool");
            assertNotNull(result);
            assertTrue(result.contains("trust_cool_on=trusted"));
            assertTrue(result.contains("trust_cool_off=trusted"));
            assertTrue(result.contains(" & "));
        }

        @Test
        @DisplayName("no-mode device: values used directly")
        void noModeDevice_valuesUsedDirectly() throws Exception {
            String result = invokeCollectIncluding(buildNoModeDevice(), "sensor_1",
                    PropertyDimension.PRIVACY, Set.of("active"), null);
            assertEquals("sensor_1.privacy_active=private", result);
        }

        @Test
        @DisplayName("returns null when no values match")
        void noMatch() throws Exception {
            String result = invokeCollectIncluding(buildMultiModeDevice(), "aircon_1",
                    PropertyDimension.TRUST, Set.of("nonexistent"), "cool");
            assertNull(result);
        }
    }

    // ── collectStatePropertyPartsExcluding ──

    @Nested
    @DisplayName("collectStatePropertyPartsExcluding")
    class ExcludingTests {

        @Test
        @DisplayName("no targetMode: excludes value from all modes that contain it")
        void noTargetMode_excludesFromAllModes() throws Exception {
            // Exclude "on" → for each mode, only off and standby remain
            String result = invokeCollectExcluding(buildMultiModeDevice(), "aircon_1",
                    PropertyDimension.TRUST, Set.of("on"), null);
            assertNotNull(result);
            assertTrue(result.contains("trust_cool_off=trusted"));
            assertTrue(result.contains("trust_cool_standby=trusted"));
            assertTrue(result.contains("trust_heat_off=trusted"));
            assertTrue(result.contains("trust_heat_standby=trusted"));
            assertFalse(result.contains("trust_cool_on=trusted"));
            assertFalse(result.contains("trust_heat_on=trusted"));
        }

        @Test
        @DisplayName("targetMode: only excludes within the specified mode")
        void targetMode_scopedExclusion() throws Exception {
            // Exclude "on" scoped to cool → only cool's off/standby, heat untouched
            String result = invokeCollectExcluding(buildMultiModeDevice(), "aircon_1",
                    PropertyDimension.TRUST, Set.of("on"), "cool");
            assertNotNull(result);
            assertTrue(result.contains("trust_cool_off=trusted"));
            assertTrue(result.contains("trust_cool_standby=trusted"));
            assertFalse(result.contains("trust_cool_on=trusted"));
            // Heat states should NOT appear (scoped to cool only)
            assertFalse(result.contains("trust_heat_"));
        }

        @Test
        @DisplayName("no targetMode: tuple exclusion resolved per-mode")
        void noTargetMode_tupleExclusion() throws Exception {
            // Exclude "on;off" → cool excludes "on", heat excludes "off"
            String result = invokeCollectExcluding(buildMultiModeDevice(), "aircon_1",
                    PropertyDimension.TRUST, Set.of("on;off"), null);
            assertNotNull(result);
            // cool: off, standby remain (on excluded)
            assertTrue(result.contains("trust_cool_off=trusted"));
            assertTrue(result.contains("trust_cool_standby=trusted"));
            assertFalse(result.contains("trust_cool_on=trusted"));
            // heat: on, standby remain (off excluded)
            assertTrue(result.contains("trust_heat_on=trusted"));
            assertTrue(result.contains("trust_heat_standby=trusted"));
            assertFalse(result.contains("trust_heat_off=trusted"));
        }

        @Test
        @DisplayName("no-mode device: excludes directly from states")
        void noModeDevice_excludesDirectly() throws Exception {
            String result = invokeCollectExcluding(buildNoModeDevice(), "sensor_1",
                    PropertyDimension.PRIVACY, Set.of("active"), null);
            assertEquals("sensor_1.privacy_idle=private", result);
        }

        @Test
        @DisplayName("returns null when all states excluded")
        void allExcluded() throws Exception {
            String result = invokeCollectExcluding(buildNoModeDevice(), "sensor_1",
                    PropertyDimension.TRUST, Set.of("active", "idle"), null);
            assertNull(result);
        }
    }

    // ── fail-closed behavior ──

    @Nested
    @DisplayName("appendRulePropertyConditions fail-closed")
    class FailClosedTests {

        private String invokeAppendRulePropertyConditions(RuleDto rule,
                                                          Map<String, DeviceSmvData> deviceSmvMap,
                                                          PropertyDimension dim) throws Exception {
            Method m = SmvMainModuleBuilder.class.getDeclaredMethod(
                    "appendRulePropertyConditions",
                    StringBuilder.class, RuleDto.class, Map.class, PropertyDimension.class);
            m.setAccessible(true);
            StringBuilder sb = new StringBuilder();
            m.invoke(builder, sb, rule, deviceSmvMap, dim);
            return sb.toString();
        }

        @Test
        @DisplayName("no conditions → TRUE")
        void noConditions_returnsTrue() throws Exception {
            RuleDto rule = RuleDto.builder().conditions(List.of()).build();
            String result = invokeAppendRulePropertyConditions(rule, Map.of(), PropertyDimension.TRUST);
            assertEquals("TRUE", result);
        }

        @Test
        @DisplayName("conditions exist but all return null property parts → FALSE (fail-closed)")
        void allNullParts_returnsFalse() throws Exception {
            DeviceSmvData device = buildMultiModeDevice();
            device.setManifest(new cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest());
            Map<String, DeviceSmvData> map = Map.of("aircon_1", device);

            // Condition with > relation on state — buildPropertyConditionPart returns null
            RuleDto.Condition cond = RuleDto.Condition.builder()
                    .deviceName("aircon_1").attribute("state").relation(">").value("5").build();
            RuleDto rule = RuleDto.builder().conditions(List.of(cond)).build();

            String result = invokeAppendRulePropertyConditions(rule, map, PropertyDimension.TRUST);
            assertEquals("FALSE", result);
        }

        @Test
        @DisplayName("conditions with valid = relation → generates property condition")
        void validEqCondition_generatesCondition() throws Exception {
            DeviceSmvData device = buildMultiModeDevice();
            device.setManifest(new cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest());
            Map<String, DeviceSmvData> map = Map.of("aircon_1", device);

            RuleDto.Condition cond = RuleDto.Condition.builder()
                    .deviceName("aircon_1").attribute("cool").relation("=").value("on").build();
            RuleDto rule = RuleDto.builder().conditions(List.of(cond)).build();

            String result = invokeAppendRulePropertyConditions(rule, map, PropertyDimension.TRUST);
            assertEquals("aircon_1.trust_cool_on=trusted", result);
        }
    }
}
