package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.board.PortableSceneTestImport;
import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvDeviceModuleBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvMainModuleBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvRuleCommentWriter;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvSpecificationBuilder;
import cn.edu.nju.Iot_Verify.component.template.DeviceTemplateSchemaValidator;
import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

public class VerifyCorrectedScene {
    private static final long USER_ID = 1L;

    @Test
    void baseline() throws Exception {
        ObjectMapper objectMapper = new ObjectMapper();
        String json = Files.readString(Paths.get("../docs/examples/elderly-care-comprehensive-scene.json"));
        JsonNode scene = objectMapper.readTree(json);

        SmvGenerator generator = buildGenerator(objectMapper, scene);
        NusmvExecutor executor = buildExecutor();

        List<DeviceVerificationDto> devices = readDevices(scene);
        List<BoardEnvironmentVariableDto> environment = readEnvironment(scene);
        List<RuleDto> rules = PortableSceneTestImport.importRules(scene);
        List<SpecificationDto> specs = PortableSceneTestImport.importSpecs(scene, "elderly", labelsByDeviceId(devices));

        SmvGenerator.GenerateResult genResult = generator.generateWithEnvironment(
            USER_ID, devices, environment, rules, specs,
            AttackScenarioDto.none(), true, SmvGenerator.GeneratePurpose.VERIFICATION);

        System.out.println("Generation: disabled=" + genResult.disabledRuleCount()
            + " skipped=" + genResult.skippedSpecCount()
            + " issues=" + genResult.generationIssues().size());

        var verifyResult = executor.execute(genResult.smvFile().toPath().toFile(), 180000);

        System.out.println("Verification: success=" + verifyResult.isSuccess());

        for (int i = 0; i < verifyResult.getSpecResults().size(); i++) {
            var spec = verifyResult.getSpecResults().get(i);
            System.out.println("  s" + (i+1) + ": " + (spec.isPassed() ? "SATISFIED" : "VIOLATED"));
        }
    }

    private SmvGenerator buildGenerator(ObjectMapper objectMapper, JsonNode scene) throws Exception {
        Map<String, String> manifests = new LinkedHashMap<>();
        for (JsonNode template : scene.path("templates")) {
            manifests.put(template.path("name").asText(),
                    objectMapper.writeValueAsString(template.path("manifest")));
        }

        SmvModelValidator modelValidator = new SmvModelValidator();
        DeviceTemplateService templateService = mock(DeviceTemplateService.class);
        when(templateService.findTemplateByName(anyLong(), anyString())).thenAnswer(invocation -> {
            String templateName = invocation.getArgument(1, String.class);
            String manifest = manifests.get(templateName);
            if (manifest == null) {
                return Optional.empty();
            }
            return Optional.of(DeviceTemplatePo.builder()
                    .id(100L)
                    .userId(USER_ID)
                    .name(templateName)
                    .manifestJson(manifest)
                    .defaultTemplate(true)
                    .build());
        });

        DeviceSmvDataFactory factory = new DeviceSmvDataFactory(
                objectMapper,
                templateService,
                modelValidator,
                new DeviceTemplateSchemaValidator(objectMapper));
        return new SmvGenerator(
                factory,
                new SmvDeviceModuleBuilder(),
                new SmvRuleCommentWriter(),
                new SmvMainModuleBuilder(),
                new SmvSpecificationBuilder(),
                modelValidator);
    }

    private NusmvExecutor buildExecutor() {
        NusmvConfig config = new NusmvConfig();
        config.setPath("NuSMV");
        config.setCommandPrefix("");
        config.setTimeoutMs(120_000);
        config.setMaxConcurrent(2);
        config.setAcquirePermitTimeoutMs(10_000);
        return new NusmvExecutor(config);
    }

    private List<DeviceVerificationDto> readDevices(JsonNode scene) {
        List<DeviceVerificationDto> devices = new ArrayList<>();
        for (JsonNode row : scene.path("devices")) {
            DeviceVerificationDto device = new DeviceVerificationDto();
            device.setVarName(row.path("id").asText());
            device.setDeviceLabel(row.path("label").asText());
            device.setTemplateName(row.path("templateName").asText());
            device.setState(textOrNull(row, "state"));
            device.setCurrentStateTrust(textOrNull(row, "currentStateTrust"));
            device.setCurrentStatePrivacy(textOrNull(row, "currentStatePrivacy"));
            device.setVariables(readVariables(row.path("variables")));
            device.setPrivacies(readPrivacies(row.path("privacies")));
            devices.add(device);
        }
        return devices;
    }

    private List<BoardEnvironmentVariableDto> readEnvironment(JsonNode scene) {
        List<BoardEnvironmentVariableDto> result = new ArrayList<>();
        for (JsonNode row : scene.path("environmentVariables")) {
            BoardEnvironmentVariableDto env = new BoardEnvironmentVariableDto();
            env.setName(row.path("name").asText());
            env.setValue(textOrNull(row, "value"));
            env.setTrust(textOrNull(row, "trust"));
            env.setPrivacy(textOrNull(row, "privacy"));
            result.add(env);
        }
        return result;
    }

    private Map<String, String> labelsByDeviceId(List<DeviceVerificationDto> devices) {
        return devices.stream().collect(java.util.stream.Collectors.toMap(
                DeviceVerificationDto::getVarName,
                DeviceVerificationDto::getDeviceLabel));
    }

    private String textOrNull(JsonNode parent, String field) {
        JsonNode node = parent.path(field);
        return node.isMissingNode() || node.isNull() ? null : node.asText();
    }

    private List<VariableStateDto> readVariables(JsonNode array) {
        List<VariableStateDto> result = new ArrayList<>();
        for (JsonNode item : array) {
            VariableStateDto dto = new VariableStateDto();
            dto.setName(item.path("name").asText());
            dto.setValue(textOrNull(item, "value"));
            dto.setTrust(textOrNull(item, "trust"));
            result.add(dto);
        }
        return result;
    }

    private List<PrivacyStateDto> readPrivacies(JsonNode array) {
        List<PrivacyStateDto> result = new ArrayList<>();
        for (JsonNode item : array) {
            PrivacyStateDto dto = new PrivacyStateDto();
            dto.setName(item.path("name").asText());
            dto.setPrivacy(textOrNull(item, "value"));
            result.add(dto);
        }
        return result;
    }
}
