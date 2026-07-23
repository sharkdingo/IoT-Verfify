package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvGenerator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvModelValidator;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvDeviceModuleBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvMainModuleBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvRuleCommentWriter;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvSpecificationBuilder;
import cn.edu.nju.Iot_Verify.component.template.DeviceTemplateSchemaValidator;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

class NusmvEnvironmentPoolTest {

    private static final long USER_ID = 7L;

    @Test
    void mergeWithDefaults_usesLowerBoundOrFirstEnumValueForMissingPoolValues() {
        DeviceManifest.InternalVariable temperature = envNumber("temperature", 15, 35);
        DeviceManifest.InternalVariable presence = DeviceManifest.InternalVariable.builder()
                .name("presence")
                .isInside(false)
                .values(List.of("away", "home"))
                .trust("untrusted")
                .privacy("private")
                .build();

        Map<String, DeviceSmvData> smvMap = new LinkedHashMap<>();
        smvMap.put("sensor_1", smv("sensor_1", "Sensor", Map.of(
                "temperature", temperature,
                "presence", presence)));

        Map<String, BoardEnvironmentVariableDto> merged = NusmvEnvironmentPool
                .mergeWithDefaults(List.of(), smvMap)
                .stream()
                .collect(Collectors.toMap(BoardEnvironmentVariableDto::getName, item -> item));

        assertEquals("15", merged.get("temperature").getValue());
        assertEquals("trusted", merged.get("temperature").getTrust());
        assertEquals("public", merged.get("temperature").getPrivacy());
        assertEquals("away", merged.get("presence").getValue());
        assertEquals("untrusted", merged.get("presence").getTrust());
        assertEquals("private", merged.get("presence").getPrivacy());
    }

    @Test
    void mergeWithDefaults_treatsUnlabeledExternalEnvironmentAsUntrusted() {
        DeviceManifest.InternalVariable externalReading = DeviceManifest.InternalVariable.builder()
                .name("externalReading")
                .isInside(false)
                .lowerBound(0)
                .upperBound(10)
                .build();
        Map<String, DeviceSmvData> smvMap = Map.of(
                "sensor_1", smv("sensor_1", "Sensor", Map.of("externalReading", externalReading)));

        BoardEnvironmentVariableDto merged = NusmvEnvironmentPool
                .mergeWithDefaults(List.of(), smvMap)
                .get(0);

        assertEquals("untrusted", merged.getTrust());
        assertEquals("public", merged.getPrivacy());
    }

    @Test
    void expandDevices_appliesEnvironmentPoolOnlyToTemplatesThatDeclareReadPermission() {
        DeviceManifest.InternalVariable temperature = envNumber("temperature", 15, 35);
        Map<String, DeviceSmvData> smvMap = new LinkedHashMap<>();
        smvMap.put("sensor_1", smv("sensor_1", "Temperature Sensor", Map.of("temperature", temperature)));
        smvMap.put("light_1", smv("light_1", "Light", Map.of()));

        List<DeviceVerificationDto> expanded = NusmvEnvironmentPool.expandDevices(
                List.of(device("sensor_1", "Temperature Sensor"), device("light_1", "Light")),
                List.of(new BoardEnvironmentVariableDto("temperature", "28", "untrusted", "private")),
                smvMap);

        DeviceVerificationDto sensor = expanded.stream()
                .filter(device -> "sensor_1".equals(device.getVarName()))
                .findFirst()
                .orElseThrow();
        DeviceVerificationDto light = expanded.stream()
                .filter(device -> "light_1".equals(device.getVarName()))
                .findFirst()
                .orElseThrow();

        assertEquals("28", sensor.getVariables().get(0).getValue());
        assertEquals("untrusted", sensor.getVariables().get(0).getTrust());
        assertEquals("private", sensor.getPrivacies().get(0).getPrivacy());
        assertNull(light.getVariables());
        assertNull(light.getPrivacies());
    }

    @Test
    void mergeWithDefaults_collectsImpactedEnvironmentEvenWhenReadableMapIsNull() {
        DeviceManifest.InternalVariable temperature = envNumber("temperature", 15, 35);
        DeviceSmvData actuator = smv("ac_1", "Air Conditioner", Map.of());
        actuator.setEnvVariables(null);
        actuator.setImpactedEnvironmentVariables(Map.of("temperature", temperature));

        Map<String, DeviceSmvData> smvMap = new LinkedHashMap<>();
        smvMap.put("ac_1", actuator);

        List<BoardEnvironmentVariableDto> merged = NusmvEnvironmentPool.mergeWithDefaults(List.of(), smvMap);

        assertEquals(1, merged.size());
        assertEquals("temperature", merged.get(0).getName());
        assertEquals("15", merged.get(0).getValue());
    }

    @Test
    void expandedEnvironmentPoolInitializesSharedSmvVariable() throws Exception {
        DeviceManifest.InternalVariable temperature = envNumber("temperature", 15, 35);
        DeviceManifest manifest = DeviceManifest.builder()
                .name("Temperature Sensor")
                .internalVariables(List.of(temperature))
                .build();
        SmvGenerator generator = generatorFor(manifest);
        List<DeviceVerificationDto> rawDevices = List.of(device("sensor_1", "Temperature Sensor"));
        Map<String, DeviceSmvData> rawMap = generator.buildDeviceSmvMap(USER_ID, rawDevices);

        List<BoardEnvironmentVariableDto> merged = NusmvEnvironmentPool.mergeWithDefaults(
                List.of(new BoardEnvironmentVariableDto("temperature", "28", "trusted", "public")),
                rawMap);
        List<DeviceVerificationDto> expanded = NusmvEnvironmentPool.expandDevices(rawDevices, merged, rawMap);
        SmvGenerator.GenerateResult generated = generator.generateWithEnvironment(
                USER_ID, expanded, merged, List.of(), List.of(), AttackScenarioDto.none(), true,
                SmvGenerator.GeneratePurpose.VERIFICATION);

        String smv = Files.readString(generated.smvFile().toPath());

        assertTrue(smv.contains("a_temperature: 15..35;"), smv);
        assertTrue(smv.contains("init(a_temperature) := 28;"), smv);
        assertTrue(smv.contains("sensor_1.temperature := a_temperature;"), smv);
    }

    @Test
    void impactedOnlyDeviceUsesOwnEnvironmentDomainWithoutReadPermission() throws Exception {
        DeviceManifest.InternalVariable temperature = envNumber("temperature", 15, 35);
        DeviceManifest sensorDomain = DeviceManifest.builder()
                .name("Temperature Sensor")
                .internalVariables(List.of(temperature))
                .build();
        DeviceManifest airConditioner = DeviceManifest.builder()
                .name("Air Conditioner")
                .modes(List.of("MachineState"))
                .initState("cool")
                .impactedVariables(List.of("temperature"))
                .environmentDomains(List.of(impactNumber("temperature", 15, 35)))
                .workingStates(List.of(
                        DeviceManifest.WorkingState.builder().name("cool").trust("trusted")
                                .privacy("public")
                                .dynamics(List.of(DeviceManifest.Dynamic.builder()
                                        .variableName("temperature").changeRate("-2").build()))
                                .build(),
                        DeviceManifest.WorkingState.builder().name("off").trust("trusted")
                                .privacy("public").build()))
                .build();

        SmvGenerator generator = generatorFor(Map.of(
                "Air Conditioner", airConditioner,
                "Temperature Sensor", sensorDomain));
        List<DeviceVerificationDto> rawDevices = List.of(device("ac_1", "Air Conditioner", "cool"));
        Map<String, DeviceSmvData> rawMap = generator.buildDeviceSmvMap(USER_ID, rawDevices);

        List<BoardEnvironmentVariableDto> merged = NusmvEnvironmentPool.mergeWithDefaults(
                List.of(new BoardEnvironmentVariableDto("temperature", "28", "trusted", "public")),
                rawMap);
        List<DeviceVerificationDto> expanded = NusmvEnvironmentPool.expandDevices(rawDevices, merged, rawMap);
        assertNull(expanded.get(0).getVariables());
        SmvGenerator.GenerateResult generated = generator.generateWithEnvironment(
                USER_ID, expanded, merged, List.of(), List.of(), AttackScenarioDto.none(), true,
                SmvGenerator.GeneratePurpose.VERIFICATION);

        String smv = Files.readString(generated.smvFile().toPath());

        assertEquals("28", merged.get(0).getValue());
        assertTrue(smv.contains("a_temperature: 15..35;"), smv);
        assertTrue(smv.contains("init(a_temperature) := 28;"), smv);
        assertTrue(smv.contains("next(ac_1.temperature_rate)"), smv);
        assertTrue(smv.contains("a_temperature+ac_1.temperature_rate"), smv);
        assertTrue(!smv.contains("ac_1.temperature := a_temperature;"), smv);
    }

    @Test
    void unrelatedTemplateCannotSupplyMissingImpactDomain() throws Exception {
        DeviceManifest sensorDomain = DeviceManifest.builder()
                .name("Temperature Sensor")
                .internalVariables(List.of(envNumber("temperature", 15, 35)))
                .build();
        DeviceManifest airConditioner = DeviceManifest.builder()
                .name("Air Conditioner")
                .modes(List.of("MachineState"))
                .initState("cool")
                .impactedVariables(List.of("temperature"))
                .workingStates(List.of(DeviceManifest.WorkingState.builder()
                        .name("cool")
                        .trust("trusted")
                        .privacy("public")
                        .dynamics(List.of(DeviceManifest.Dynamic.builder()
                                .variableName("temperature")
                                .changeRate("-2")
                                .build()))
                        .build()))
                .build();
        SmvGenerator generator = generatorFor(Map.of(
                "Air Conditioner", airConditioner,
                "Temperature Sensor", sensorDomain));
        List<DeviceVerificationDto> devices = List.of(device("ac_1", "Air Conditioner", "cool"));

        cn.edu.nju.Iot_Verify.exception.BadRequestException exception = assertThrows(
                cn.edu.nju.Iot_Verify.exception.BadRequestException.class, () ->
                generator.generateWithEnvironment(
                        USER_ID, devices,
                        List.of(new BoardEnvironmentVariableDto("temperature", "28", "trusted", "public")),
                        List.of(), List.of(), AttackScenarioDto.none(), true,
                        SmvGenerator.GeneratePurpose.VERIFICATION));

        assertTrue(exception.getMessage().contains("unknown or non-writable"), exception.getMessage());
    }

    private static DeviceManifest.InternalVariable envNumber(String name, int lower, int upper) {
        return DeviceManifest.InternalVariable.builder()
                .name(name)
                .isInside(false)
                .falsifiableWhenCompromised(true)
                .lowerBound(lower)
                .upperBound(upper)
                .trust("trusted")
                .privacy("public")
                .build();
    }

    private static DeviceManifest.EnvironmentDomain impactNumber(String name, int lower, int upper) {
        return DeviceManifest.EnvironmentDomain.builder()
                .name(name)
                .lowerBound(lower)
                .upperBound(upper)
                .trust("trusted")
                .privacy("public")
                .build();
    }

    private static DeviceSmvData smv(String varName,
                                     String templateName,
                                     Map<String, DeviceManifest.InternalVariable> envVariables) {
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName(varName);
        smv.setTemplateName(templateName);
        smv.setModuleName(templateName.replace(" ", "") + "_" + varName);
        smv.setModes(List.of());
        smv.setVariables(List.copyOf(envVariables.values()));
        smv.setEnvVariables(new LinkedHashMap<>(envVariables));
        smv.setManifest(DeviceManifest.builder()
                .name(templateName)
                .internalVariables(List.copyOf(envVariables.values()))
                .build());
        return smv;
    }

    private static DeviceVerificationDto device(String varName, String templateName) {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName(varName);
        device.setTemplateName(templateName);
        return device;
    }

    private static DeviceVerificationDto device(String varName, String templateName, String state) {
        DeviceVerificationDto device = device(varName, templateName);
        device.setState(state);
        return device;
    }

    private static SmvGenerator generatorFor(DeviceManifest manifest) throws Exception {
        return generatorFor(Map.of("Temperature Sensor", manifest));
    }

    private static SmvGenerator generatorFor(Map<String, DeviceManifest> manifests) throws Exception {
        ObjectMapper objectMapper = new ObjectMapper();
        DeviceTemplateService templateService = mock(DeviceTemplateService.class);
        when(templateService.findTemplateByName(anyLong(), anyString())).thenAnswer(invocation -> {
            String name = invocation.getArgument(1, String.class);
            DeviceManifest manifest = manifests.get(name);
            if (manifest == null) {
                return Optional.empty();
            }
            return Optional.of(DeviceTemplatePo.builder()
                    .id(1L)
                    .userId(USER_ID)
                    .name(name)
                    .manifestJson(objectMapper.writeValueAsString(manifest))
                    .defaultTemplate(true)
                    .build());
        });
        SmvModelValidator validator = new SmvModelValidator();
        return new SmvGenerator(
                new DeviceSmvDataFactory(objectMapper, templateService, validator,
                        new DeviceTemplateSchemaValidator(objectMapper)),
                new SmvDeviceModuleBuilder(),
                new SmvRuleCommentWriter(),
                new SmvMainModuleBuilder(),
                new SmvSpecificationBuilder(),
                validator);
    }
}
