package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvDeviceModuleBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvMainModuleBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvRuleCommentWriter;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvSpecificationBuilder;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.exception.SmvGenerationException;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.lang.reflect.Method;
import java.util.*;

import static org.junit.jupiter.api.Assertions.*;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.eq;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

/**
 * SmvGenerator 五项修复的单元测试。
 * 纯 POJO 构造，不依赖 Spring 上下文。
 */
class SmvGeneratorFixesTest {

    private SmvModelValidator validator;
    private SmvMainModuleBuilder mainBuilder;
    private SmvDeviceModuleBuilder deviceBuilder;
    private SmvSpecificationBuilder specBuilder;

    @BeforeEach
    void setUp() {
        validator = new SmvModelValidator();
        mainBuilder = new SmvMainModuleBuilder();
        deviceBuilder = new SmvDeviceModuleBuilder();
        specBuilder = new SmvSpecificationBuilder();
    }

    // ======================== helpers ========================

    private DeviceManifest.InternalVariable numericVar(String name, boolean isInside, int lo, int hi) {
        return DeviceManifest.InternalVariable.builder()
                .name(name).isInside(isInside).lowerBound(lo).upperBound(hi).build();
    }

    private DeviceManifest.InternalVariable enumVar(String name, boolean isInside, String... vals) {
        return DeviceManifest.InternalVariable.builder()
                .name(name).isInside(isInside).values(Arrays.asList(vals)).build();
    }

    /** 构建一个最小的 DeviceSmvData（单 mode 或多 mode） */
    private DeviceSmvData buildSmvData(String varName, String templateName,
                                       List<String> modes,
                                       Map<String, List<String>> modeStates,
                                       List<DeviceManifest.InternalVariable> vars,
                                       DeviceManifest manifest) {
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName(varName);
        smv.setTemplateName(templateName);
        smv.setModuleName(templateName + "_" + varName);
        smv.getModes().addAll(modes);
        smv.getModeStates().putAll(modeStates);
        smv.getVariables().addAll(vars);
        smv.setManifest(manifest);
        smv.setSensor(manifest.getApis() == null || manifest.getApis().isEmpty());
        return smv;
    }

    // ======================== P1: Trigger.Attribute 合法性 ========================

    @Test
    @DisplayName("P1: legal trigger attribute passes validation")
    void triggerAttribute_legal_passes() {
        DeviceManifest manifest = DeviceManifest.builder()
                .modes(List.of("Mode"))
                .internalVariables(List.of(numericVar("temperature", false, 0, 50)))
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("on").trust("trusted").build(),
                        DeviceManifest.WorkingState.builder().name("off").trust("trusted").build()))
                .transitions(List.of(DeviceManifest.Transition.builder()
                        .name("t1").startState("on").endState("off")
                        .trigger(DeviceManifest.Trigger.builder()
                                .attribute("temperature").relation("=").value("50").build())
                        .build()))
                .build();

        DeviceSmvData smv = buildSmvData("clock_1", "Clock",
                List.of("Mode"), Map.of("Mode", List.of("on", "off")),
                List.of(numericVar("temperature", false, 0, 50)), manifest);

        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("clock_1", smv);
        assertDoesNotThrow(() -> validator.validate(map));
    }

    @Test
    @DisplayName("P1: illegal trigger attribute throws SmvGenerationException")
    void triggerAttribute_illegal_throws() {
        DeviceManifest manifest = DeviceManifest.builder()
                .modes(List.of("Mode"))
                .internalVariables(List.of(numericVar("temperature", false, 0, 50)))
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("on").trust("trusted").build()))
                .transitions(List.of(DeviceManifest.Transition.builder()
                        .name("t1").startState("on").endState("on")
                        .trigger(DeviceManifest.Trigger.builder()
                                .attribute("nonexistent").relation("=").value("1").build())
                        .build()))
                .build();

        DeviceSmvData smv = buildSmvData("dev_1", "Dev",
                List.of("Mode"), Map.of("Mode", List.of("on")),
                List.of(numericVar("temperature", false, 0, 50)), manifest);

        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("dev_1", smv);
        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> validator.validate(map));
        assertTrue(ex.getMessage().contains("nonexistent"));
        assertTrue(ex.getMessage().contains("t1"));
    }

    // ======================== P2: StartState/EndState 格式 ========================

    @Test
    @DisplayName("P2: multi-mode API EndState wrong segment count throws")
    void multiModeEndState_wrongSegments_throws() {
        DeviceManifest manifest = DeviceManifest.builder()
                .modes(List.of("Mode", "State"))
                .internalVariables(List.of())
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("auto;cool").trust("trusted").build()))
                .apis(List.of(DeviceManifest.API.builder()
                        .name("setAuto").startState("auto;cool")
                        // 只有 1 段，但设备有 2 个 mode → 应报错
                        .endState("auto")
                        .build()))
                .build();

        DeviceSmvData smv = buildSmvData("thermo_1", "Thermostat",
                List.of("Mode", "State"),
                Map.of("Mode", List.of("auto"), "State", List.of("cool")),
                List.of(), manifest);

        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("thermo_1", smv);
        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> validator.validate(map));
        assertTrue(ex.getMessage().contains("1 segments"));
        assertTrue(ex.getMessage().contains("expected 2"));
    }

    // ======================== P3: env var 冲突检测 ========================

    @Test
    @DisplayName("P3: same-name env var with different range throws")
    void envVarConflict_differentRange_throws() {
        DeviceManifest.InternalVariable timeA = numericVar("time", false, 0, 23);
        DeviceManifest.InternalVariable timeB = numericVar("time", false, 0, 47);

        DeviceManifest mA = DeviceManifest.builder()
                .modes(List.of("Mode"))
                .internalVariables(List.of(timeA))
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("on").trust("trusted").build()))
                .build();
        DeviceManifest mB = DeviceManifest.builder()
                .modes(List.of("Mode"))
                .internalVariables(List.of(timeB))
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("on").trust("trusted").build()))
                .build();

        DeviceSmvData smvA = buildSmvData("clock_1", "Clock",
                List.of("Mode"), Map.of("Mode", List.of("on")),
                List.of(timeA), mA);
        smvA.getEnvVariables().put("time", timeA);

        DeviceSmvData smvB = buildSmvData("sensor_1", "Sensor",
                List.of("Mode"), Map.of("Mode", List.of("on")),
                List.of(timeB), mB);
        smvB.getEnvVariables().put("time", timeB);

        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("clock_1", smvA);
        map.put("sensor_1", smvB);

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> validator.validate(map));
        assertTrue(ex.getMessage().contains("range mismatch"));
        assertTrue(ex.getMessage().contains("time"));
    }

    @Test
    @DisplayName("P3: same-name env var with same range passes")
    void envVarConflict_sameRange_passes() {
        DeviceManifest.InternalVariable timeA = numericVar("time", false, 0, 23);
        DeviceManifest.InternalVariable timeB = numericVar("time", false, 0, 23);

        DeviceManifest mA = DeviceManifest.builder()
                .modes(List.of("Mode"))
                .internalVariables(List.of(timeA))
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("on").trust("trusted").build()))
                .build();
        DeviceManifest mB = DeviceManifest.builder()
                .modes(List.of("Mode"))
                .internalVariables(List.of(timeB))
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("on").trust("trusted").build()))
                .build();

        DeviceSmvData smvA = buildSmvData("clock_1", "Clock",
                List.of("Mode"), Map.of("Mode", List.of("on")),
                List.of(timeA), mA);
        smvA.getEnvVariables().put("time", timeA);

        DeviceSmvData smvB = buildSmvData("sensor_1", "Sensor",
                List.of("Mode"), Map.of("Mode", List.of("on")),
                List.of(timeB), mB);
        smvB.getEnvVariables().put("time", timeB);

        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("clock_1", smvA);
        map.put("sensor_1", smvB);

        assertDoesNotThrow(() -> validator.validate(map));
    }

    // ======================== P4: env transition 用 a_var ========================

    @Test
    @DisplayName("P4: env transition condition uses a_time instead of clock_1.time")
    void envTransition_usesAVar() {
        DeviceManifest.InternalVariable timeVar = numericVar("time", false, 0, 23);
        DeviceManifest manifest = DeviceManifest.builder()
                .modes(List.of("Mode"))
                .internalVariables(List.of(timeVar))
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("running").trust("trusted").build()))
                .transitions(List.of(DeviceManifest.Transition.builder()
                        .name("reset")
                        .trigger(DeviceManifest.Trigger.builder()
                                .attribute("time").relation("=").value("23").build())
                        .assignments(List.of(DeviceManifest.Assignment.builder()
                                .attribute("time").value("0").build()))
                        .build()))
                .apis(List.of(DeviceManifest.API.builder()
                        .name("start").startState("running").endState("running").build()))
                .build();

        DeviceSmvData smv = buildSmvData("clock_1", "Clock",
                List.of("Mode"), Map.of("Mode", List.of("running")),
                List.of(timeVar), manifest);
        smv.getEnvVariables().put("time", timeVar);
        smv.getCurrentModeStates().put("Mode", "running");

        DeviceVerificationDto dto = new DeviceVerificationDto();
        dto.setVarName("clock_1");
        dto.setTemplateName("Clock");
        dto.setState("running");

        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("clock_1", smv);

        String result = mainBuilder.build(1L, List.of(dto), List.of(), map, false, 0, false);

        // P4 核心断言：条件应为 a_time = 23，而非 clock_1.time = 23
        assertTrue(result.contains("a_time = 23"), "Should use a_time, got:\n" + result);
        assertFalse(result.contains("clock_1.time = 23"), "Should NOT use clock_1.time");
    }

    // ======================== P5: trust/privacy next=self ========================

    @Test
    @DisplayName("P5: multi-mode actuator trust has next() with self-hold")
    void trustNextSelfHold_multiMode() {
        DeviceManifest manifest = DeviceManifest.builder()
                .modes(List.of("Mode", "State"))
                .internalVariables(List.of())
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("home;idle").trust("trusted").build(),
                        DeviceManifest.WorkingState.builder().name("away;active").trust("untrusted").build()))
                .apis(List.of(DeviceManifest.API.builder()
                        .name("goHome").startState("away;active").endState("home;idle").build()))
                .build();

        DeviceSmvData smv = buildSmvData("lock_1", "Lock",
                List.of("Mode", "State"),
                Map.of("Mode", List.of("home", "away"), "State", List.of("idle", "active")),
                List.of(), manifest);
        smv.getCurrentModeStates().put("Mode", "home");
        smv.getCurrentModeStates().put("State", "idle");
        smv.setInstanceStateTrust("trusted");

        DeviceVerificationDto dto = new DeviceVerificationDto();
        dto.setVarName("lock_1");
        dto.setTemplateName("Lock");
        dto.setState("home;idle");

        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("lock_1", smv);

        String result = mainBuilder.build(1L, List.of(dto), List.of(), map, false, 0, false);

        // P5 核心断言：trust_Mode_home 必须有 next() 且包含自保持
        assertTrue(result.contains("next(lock_1.trust_Mode_home)"),
                "Should have next() for trust_Mode_home, got:\n" + result);
        assertTrue(result.contains("TRUE: lock_1.trust_Mode_home;"),
                "Should self-hold trust_Mode_home, got:\n" + result);
    }

    @Test
    @DisplayName("P5: trust conflict in WorkingStates throws")
    void trustConflict_throws() {
        DeviceManifest manifest = DeviceManifest.builder()
                .modes(List.of("Mode", "State"))
                .internalVariables(List.of())
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("home;idle").trust("trusted").build(),
                        // 同一个 Mode_home 出现不同 trust
                        DeviceManifest.WorkingState.builder().name("home;active").trust("untrusted").build()))
                .apis(List.of(DeviceManifest.API.builder()
                        .name("act").startState("home;idle").endState("home;active").build()))
                .build();

        DeviceSmvData smv = buildSmvData("lock_1", "Lock",
                List.of("Mode", "State"),
                Map.of("Mode", List.of("home"), "State", List.of("idle", "active")),
                List.of(), manifest);

        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("lock_1", smv);

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> validator.validate(map));
        assertTrue(ex.getMessage().contains("trust/privacy conflict"));
        assertTrue(ex.getMessage().contains("Mode_home"));
    }

    // ======================== P6: privacy spec + enablePrivacy=false ========================

    /** 通过反射调用 SmvGenerator.validateNoPrivacySpecs */
    private void invokeValidateNoPrivacySpecs(List<SpecificationDto> specs) throws Exception {
        // SmvGenerator 的构造函数需要所有依赖，但 validateNoPrivacySpecs 不使用它们
        SmvGenerator generator = new SmvGenerator(null, null, null, null, null, null);
        Method method = SmvGenerator.class.getDeclaredMethod("validateNoPrivacySpecs", List.class);
        method.setAccessible(true);
        try {
            method.invoke(generator, specs);
        } catch (java.lang.reflect.InvocationTargetException e) {
            if (e.getCause() instanceof SmvGenerationException) {
                throw (SmvGenerationException) e.getCause();
            }
            throw e;
        }
    }

    private SpecConditionDto makeCondition(String targetType) {
        SpecConditionDto cond = new SpecConditionDto();
        cond.setDeviceId("dev1");
        cond.setTargetType(targetType);
        cond.setKey("temperature");
        cond.setRelation("=");
        cond.setValue("trusted");
        return cond;
    }

    @Test
    @DisplayName("P6: privacy condition in aConditions throws when privacy disabled")
    void privacyInAConditions_throws() {
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_privacy_1");
        spec.setAConditions(List.of(makeCondition("privacy")));
        spec.setIfConditions(List.of());
        spec.setThenConditions(List.of());

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> invokeValidateNoPrivacySpecs(List.of(spec)));
        assertTrue(ex.getMessage().contains("spec_privacy_1"));
        assertTrue(ex.getMessage().contains("privacy"));
        assertEquals("PRIVACY_SPEC_WITHOUT_PRIVACY", ex.getErrorCategory());
    }

    @Test
    @DisplayName("P6: privacy condition in ifConditions throws when privacy disabled")
    void privacyInIfConditions_throws() {
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_privacy_2");
        spec.setAConditions(List.of());
        spec.setIfConditions(List.of(makeCondition("privacy")));
        spec.setThenConditions(List.of());

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> invokeValidateNoPrivacySpecs(List.of(spec)));
        assertTrue(ex.getMessage().contains("spec_privacy_2"));
    }

    @Test
    @DisplayName("P6: privacy condition in thenConditions throws when privacy disabled")
    void privacyInThenConditions_throws() {
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_privacy_3");
        spec.setAConditions(List.of());
        spec.setIfConditions(List.of());
        spec.setThenConditions(List.of(makeCondition("privacy")));

        SmvGenerationException ex = assertThrows(SmvGenerationException.class,
                () -> invokeValidateNoPrivacySpecs(List.of(spec)));
        assertTrue(ex.getMessage().contains("spec_privacy_3"));
    }

    @Test
    @DisplayName("P6: non-privacy specs pass validation")
    void nonPrivacySpecs_passes() {
        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_trust_1");
        spec.setAConditions(List.of(makeCondition("trust")));
        spec.setIfConditions(List.of(makeCondition("state")));
        spec.setThenConditions(List.of(makeCondition("variable")));

        assertDoesNotThrow(() -> invokeValidateNoPrivacySpecs(List.of(spec)));
    }

    @Test
    @DisplayName("P6: empty specs list passes validation")
    void emptySpecs_passes() {
        assertDoesNotThrow(() -> invokeValidateNoPrivacySpecs(List.of()));
    }

    // ======================== P7: intensity=0 时 INVAR 约束 ========================

    /** 构建最小传感器设备用于 intensity 测试 */
    private DeviceSmvData buildSensorSmvForIntensity(String varName, int lo, int hi) {
        DeviceManifest manifest = DeviceManifest.builder()
                .modes(List.of("Mode"))
                .internalVariables(List.of(numericVar("temperature", false, lo, hi)))
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("on").trust("trusted").build()))
                .build();
        DeviceSmvData smv = buildSmvData(varName, "Sensor",
                List.of("Mode"),
                Map.of("Mode", List.of("on")),
                List.of(numericVar("temperature", false, lo, hi)),
                manifest);
        smv.getCurrentModeStates().put("Mode", "on");
        smv.setInstanceStateTrust("trusted");
        return smv;
    }

    @Test
    @DisplayName("P7: isAttack=true, intensity=0 generates FROZENVAR + INVAR intensity<=0")
    void attackWithZeroIntensity_generatesInvarZero() {
        DeviceSmvData smv = buildSensorSmvForIntensity("ts_1", 0, 100);
        DeviceVerificationDto dto = new DeviceVerificationDto();
        dto.setVarName("ts_1");
        dto.setTemplateName("Sensor");
        dto.setState("on");

        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("ts_1", smv);

        String result = mainBuilder.build(1L, List.of(dto), List.of(), map, true, 0, false);

        assertTrue(result.contains("FROZENVAR"), "Should declare FROZENVAR section");
        assertTrue(result.contains("intensity: 0..50"), "Should declare intensity variable");
        assertTrue(result.contains("INVAR intensity <= 0"), "Should constrain intensity to 0");
        assertTrue(result.contains("init(intensity)"), "Should initialize intensity");
    }

    @Test
    @DisplayName("P7: isAttack=true, intensity=3 generates INVAR intensity<=3")
    void attackWithPositiveIntensity_generatesCorrectInvar() {
        DeviceSmvData smv = buildSensorSmvForIntensity("ts_1", 0, 100);
        DeviceVerificationDto dto = new DeviceVerificationDto();
        dto.setVarName("ts_1");
        dto.setTemplateName("Sensor");
        dto.setState("on");

        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("ts_1", smv);

        String result = mainBuilder.build(1L, List.of(dto), List.of(), map, true, 3, false);

        assertTrue(result.contains("INVAR intensity <= 3"), "Should constrain intensity to 3");
    }

    // ======================== P8: 规格不再注入 intensity ========================

    @Test
    @DisplayName("P8: spec does not contain intensity injection in antecedent")
    void specNoIntensityInjection() {
        SpecConditionDto cond = new SpecConditionDto();
        cond.setDeviceId("ts_1");
        cond.setTargetType("variable");
        cond.setKey("temperature");
        cond.setRelation("GT");
        cond.setValue("30");

        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_1");
        spec.setTemplateId("1"); // AG(A)
        spec.setAConditions(List.of(cond));
        spec.setIfConditions(List.of());
        spec.setThenConditions(List.of());

        DeviceSmvData smv = buildSensorSmvForIntensity("ts_1", 0, 100);
        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("ts_1", smv);

        String result = specBuilder.build(List.of(spec), true, 3, map);

        assertFalse(result.contains("intensity<="), "Spec should not inject intensity constraint");
    }

    @Test
    @DisplayName("P8: templateId=7 safety spec does not contain intensity injection")
    void safetySpecNoIntensityInjection() {
        SpecConditionDto cond = new SpecConditionDto();
        cond.setDeviceId("ts_1");
        cond.setTargetType("variable");
        cond.setKey("temperature");
        cond.setRelation("GT");
        cond.setValue("30");

        SpecificationDto spec = new SpecificationDto();
        spec.setId("spec_7");
        spec.setTemplateId("7");
        spec.setAConditions(List.of(cond));
        spec.setIfConditions(List.of());
        spec.setThenConditions(List.of());

        DeviceSmvData smv = buildSensorSmvForIntensity("ts_1", 0, 100);
        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        map.put("ts_1", smv);

        String result = specBuilder.build(List.of(spec), true, 3, map);

        assertFalse(result.contains("intensity<="), "Safety spec should not inject intensity constraint");
        assertTrue(result.contains(".is_attack=FALSE"), "Safety spec should still include is_attack guard");
    }

    // ======================== P9: 范围扩展按 intensity 缩放 ========================

    @Test
    @DisplayName("P9: intensity=0 produces no range expansion for sensor")
    void rangeExpansion_zeroIntensity_noExpansion() {
        DeviceSmvData smv = buildSensorSmvForIntensity("ts_1", 0, 100);
        String result = deviceBuilder.build(smv, true, 0, false);

        // temperature: 0..100 — no expansion
        assertTrue(result.contains("0..100"), "intensity=0 should not expand range");
        assertFalse(result.contains("0..120"), "intensity=0 should not have old expansion");
    }

    @Test
    @DisplayName("P9: intensity=50 produces max range expansion for sensor")
    void rangeExpansion_maxIntensity_fullExpansion() {
        DeviceSmvData smv = buildSensorSmvForIntensity("ts_1", 0, 100);
        String result = deviceBuilder.build(smv, true, 50, false);

        // range=100, expansion = (int)(100/5.0 * 50/50.0) = 20, upper = 120
        assertTrue(result.contains("0..120"), "intensity=50 should expand range to 120");
    }

    // ======================== P10: SmvGenerator intensity clamp ========================

    private SmvGenerator buildGeneratorForClampTests() throws Exception {
        ObjectMapper mapper = new ObjectMapper();
        DeviceTemplateService templateService = mock(DeviceTemplateService.class);

        DeviceManifest manifest = DeviceManifest.builder()
                .modes(List.of("Mode"))
                .initState("on")
                .internalVariables(List.of(numericVar("temperature", true, 0, 100)))
                .workingStates(List.of(DeviceManifest.WorkingState.builder()
                        .name("on").trust("trusted").build()))
                .build();

        DeviceTemplatePo template = DeviceTemplatePo.builder()
                .userId(1L)
                .name("SensorTemplate")
                .manifestJson(mapper.writeValueAsString(manifest))
                .build();

        when(templateService.findTemplateByName(anyLong(), eq("SensorTemplate")))
                .thenReturn(Optional.of(template));

        DeviceSmvDataFactory factory = new DeviceSmvDataFactory(mapper, templateService, new SmvModelValidator());
        return new SmvGenerator(
                factory,
                new SmvDeviceModuleBuilder(),
                new SmvRuleCommentWriter(),
                new SmvMainModuleBuilder(),
                new SmvSpecificationBuilder(),
                new SmvModelValidator()
        );
    }

    private DeviceVerificationDto buildClampTestDevice() {
        DeviceVerificationDto dto = new DeviceVerificationDto();
        dto.setVarName("ts_1");
        dto.setTemplateName("SensorTemplate");
        dto.setState("on");
        return dto;
    }

    @Test
    @DisplayName("P10: SmvGenerator clamps intensity>50 to 50")
    void generatorClamp_upperBound() throws Exception {
        SmvGenerator generator = buildGeneratorForClampTests();
        DeviceVerificationDto dto = buildClampTestDevice();

        SmvGenerator.GenerateResult gen = generator.generate(
                1L, List.of(dto), List.of(), List.of(), true, 999, false);
        String smv = Files.readString(gen.smvFile().toPath());

        assertTrue(smv.contains("INVAR intensity <= 50;"), "Upper bound should clamp to 50");
        assertTrue(smv.contains("temperature: 0..120;"), "Clamp=50 should produce full range expansion");
    }

    @Test
    @DisplayName("P10: SmvGenerator clamps intensity<0 to 0")
    void generatorClamp_lowerBound() throws Exception {
        SmvGenerator generator = buildGeneratorForClampTests();
        DeviceVerificationDto dto = buildClampTestDevice();

        SmvGenerator.GenerateResult gen = generator.generate(
                1L, List.of(dto), List.of(), List.of(), true, -7, false);
        String smv = Files.readString(gen.smvFile().toPath());

        assertTrue(smv.contains("INVAR intensity <= 0;"), "Lower bound should clamp to 0");
        assertTrue(smv.contains("temperature: 0..100;"), "Clamp=0 should produce no range expansion");
    }
}
