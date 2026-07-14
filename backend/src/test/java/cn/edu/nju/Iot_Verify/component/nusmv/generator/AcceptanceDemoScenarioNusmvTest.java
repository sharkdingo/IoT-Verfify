package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.RuleFixer;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.localize.FaultLocalizer;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy.RemoveRulesFixStrategy;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvDeviceModuleBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvMainModuleBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvRuleCommentWriter;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.module.SmvSpecificationBuilder;
import cn.edu.nju.Iot_Verify.component.nusmv.parser.SmvTraceParser;
import cn.edu.nju.Iot_Verify.component.template.DeviceTemplateSchemaValidator;
import cn.edu.nju.Iot_Verify.configure.FixConfig;
import cn.edu.nju.Iot_Verify.configure.NusmvConfig;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixResultDto;
import cn.edu.nju.Iot_Verify.dto.fix.FixSuggestionDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.po.DeviceTemplatePo;
import cn.edu.nju.Iot_Verify.service.DeviceTemplateService;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.api.Test;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

class AcceptanceDemoScenarioNusmvTest {

    private static final long USER_ID = 1L;
    private static final Path SCENE_PATH =
            Path.of("..", "docs", "examples", "acceptance-demo-scene.json");
    private static final Path MULTI_VIOLATION_SCENE_PATH =
            Path.of("..", "docs", "examples", "multi-violation-repair-scene.json");
    private static final List<AdditionalScenarioExpectation> ADDITIONAL_SCENARIOS = List.of(
            new AdditionalScenarioExpectation(
                    "fire",
                    Path.of("..", "docs", "examples", "default-fire-evacuation-scene.json"),
                    4, 2, 3, 5, 1, 4,
                    "door_1", "unlocked",
                    "When the alarm sounds, unlock the front door for evacuation",
                    2),
            new AdditionalScenarioExpectation(
                    "climate",
                    Path.of("..", "docs", "examples", "default-climate-conflict-scene.json"),
                    2, 2, 2, 4, 2, 3,
                    "ac_1", "heat",
                    "Unsafe conflicting rule: when the room is hot, heat the living room",
                    1),
            new AdditionalScenarioExpectation(
                    "rfid",
                    Path.of("..", "docs", "examples", "default-rfid-access-scene.json"),
                    3, 0, 2, 5, 0, 3,
                    "door_1", "unlocked",
                    null,
                    2));
    @Test
    void acceptanceScene_supportsVerificationSimulationAnimationAttackAndVerifiedRepair() throws Exception {
        String nusmvPath = resolveNusmvPath();
        Assumptions.assumeTrue(nusmvPath != null && Files.exists(Path.of(nusmvPath)),
                "NuSMV executable is required for this acceptance smoke test");

        ObjectMapper objectMapper = new ObjectMapper();
        JsonNode scene = objectMapper.readTree(Files.readString(SCENE_PATH));
        assertEquals("iot-verify.board-scene", scene.path("schema").asText());
        assertEquals(4, scene.path("version").asInt());
        assertEquals(4, scene.path("devices").size());
        assertEquals(3, scene.path("rules").size());
        assertEquals(5, scene.path("specs").size());

        SmvGenerator generator = buildGenerator(objectMapper, scene);
        NusmvExecutor executor = buildExecutor(nusmvPath);
        List<DeviceVerificationDto> devices = readDevices(scene);
        List<BoardEnvironmentVariableDto> environment = readEnvironment(scene);
        List<RuleDto> rules = readRules(scene);
        List<SpecificationDto> specs = readSpecs(scene, devices, "acceptance");

        SmvGenerator.GenerateResult generated = generator.generateWithEnvironment(
                USER_ID, devices, environment, rules, specs,
                false, 0, true, SmvGenerator.GeneratePurpose.VERIFICATION);
        assertEquals(0, generated.disabledRuleCount());
        assertEquals(0, generated.skippedSpecCount());

        NusmvExecutor.NusmvResult verification = executor.execute(generated.smvFile());
        assertTrue(verification.isSuccess(), verification::getErrorMessage);
        assertEquals(specs.size(), verification.getSpecResults().size());
        assertEquals(1, verification.getSpecResults().stream().filter(result -> !result.isPassed()).count());

        NusmvExecutor.SpecCheckResult cameraViolation = verification.getSpecResults().stream()
                .filter(result -> !result.isPassed())
                .findFirst()
                .orElseThrow();
        assertTrue(cameraViolation.getSpecExpression().contains("camera_1.MachineState = takingphoto"));
        assertNotNull(cameraViolation.getCounterexample());

        SmvTraceParser traceParser = new SmvTraceParser();
        List<TraceStateDto> counterexampleStates = traceParser.parseCounterexampleStates(
                cameraViolation.getCounterexample(), generated.deviceSmvMap(), rules);
        assertTrue(counterexampleStates.size() >= 2, "The violation must produce an animatable trace");
        assertTrue(counterexampleStates.stream()
                .flatMap(state -> state.getDevices().stream())
                .anyMatch(device -> "camera_1".equals(device.getDeviceId())
                        && "takingphoto".equals(device.getState())));

        SmvGenerator.GenerateResult simulationModel = generator.generateWithEnvironment(
                USER_ID, devices, environment, rules, specs,
                false, 0, true, SmvGenerator.GeneratePurpose.SIMULATION);
        NusmvExecutor.SimulationOutput simulation =
                executor.executeInteractiveSimulation(simulationModel.smvFile(), 6);
        assertTrue(simulation.isSuccess(), simulation::getErrorMessage);
        List<TraceStateDto> simulationStates = traceParser.parseCounterexampleStates(
                simulation.getTraceText(), simulationModel.deviceSmvMap(), rules);
        assertTrue(simulationStates.size() >= 2, "Simulation must produce an animatable model trajectory");
        assertTrue(hasDeviceState(simulationStates, "camera_1", "takingphoto"),
                "The simulation should show the camera-photo step");
        assertTrue(hasDeviceState(simulationStates, "alarm_1", "siren"),
                "The simulation should show the alarm step");
        assertTrue(hasDeviceState(simulationStates, "light_1", "on"),
                "The simulation should show the light step");

        SmvGenerator.GenerateResult attackedModel = generator.generateWithEnvironment(
                USER_ID, devices, environment, rules, specs,
                true, 1, true, SmvGenerator.GeneratePurpose.VERIFICATION);
        NusmvExecutor.NusmvResult attackedVerification = executor.execute(attackedModel.smvFile());
        assertTrue(attackedVerification.isSuccess(), attackedVerification::getErrorMessage);
        assertEquals(specs.size(), attackedVerification.getSpecResults().size());
        assertEquals(4, attackedVerification.getSpecResults().stream()
                .filter(result -> !result.isPassed()).count(),
                "Budget-one attack branches should expose source-label and automation-link failures");

        FixConfig fixConfig = new FixConfig();
        fixConfig.setFixTimeoutMs(120_000);
        RuleFixer fixer = new RuleFixer(
                new FaultLocalizer(),
                List.of(new RemoveRulesFixStrategy(generator, executor)),
                fixConfig);
        FixResultDto fixResult = fixer.fix(
                1L,
                specs.get(0).getId(),
                counterexampleStates,
                rules,
                devices,
                environment,
                specs,
                generated.deviceSmvMap(),
                USER_ID,
                false,
                0,
                true,
                List.of("remove"),
                10,
                Map.of());
        assertTrue(fixResult.isFixable(), fixResult::getSummary);
        assertEquals(1, fixResult.getFaultRules().size(),
                "The camera violation should localize only the photo automation");
        assertTrue(fixResult.getUnusedPreferredRangeSelections().isEmpty(),
                "An omitted preference list must serialize as an empty result collection");

        FixSuggestionDto removal = fixResult.getSuggestions().stream()
                .filter(suggestion -> "remove".equals(suggestion.getStrategy()))
                .findFirst()
                .orElseThrow();
        assertTrue(removal.isVerified());
        assertEquals(List.of(0), removal.getRemovedRuleIndices());

        Set<Integer> removedIndices = new HashSet<>(removal.getRemovedRuleIndices());
        List<RuleDto> repairedRules = new ArrayList<>();
        for (int index = 0; index < rules.size(); index++) {
            if (!removedIndices.contains(index)) {
                repairedRules.add(rules.get(index));
            }
        }
        assertEquals(2, repairedRules.size());

        SmvGenerator.GenerateResult repairedModel = generator.generateWithEnvironment(
                USER_ID, devices, environment, repairedRules, specs,
                false, 0, true, SmvGenerator.GeneratePurpose.VERIFICATION);
        NusmvExecutor.NusmvResult repairedVerification = executor.execute(repairedModel.smvFile());
        assertTrue(repairedVerification.isSuccess(), repairedVerification::getErrorMessage);
        assertFalse(repairedVerification.hasAnyViolation(),
                "The verified removal suggestion must make every emitted demo specification pass");
    }

    @Test
    void multiViolationScene_hasTwoCounterexamplesAndOneVerifiedRootCauseRemoval() throws Exception {
        String nusmvPath = resolveNusmvPath();
        Assumptions.assumeTrue(nusmvPath != null && Files.exists(Path.of(nusmvPath)),
                "NuSMV executable is required for the multi-violation scene regression");

        ObjectMapper objectMapper = new ObjectMapper();
        JsonNode scene = objectMapper.readTree(Files.readString(MULTI_VIOLATION_SCENE_PATH));
        assertEquals("iot-verify.board-scene", scene.path("schema").asText());
        assertEquals(4, scene.path("version").asInt());
        assertEquals(4, scene.path("devices").size());
        assertEquals(2, scene.path("environmentVariables").size());
        assertEquals(3, scene.path("rules").size());
        assertEquals(5, scene.path("specs").size());
        assertEquals("untrusted", scene.path("environmentVariables").get(1).path("trust").asText());

        SmvGenerator generator = buildGenerator(objectMapper, scene);
        NusmvExecutor executor = buildExecutor(nusmvPath);
        List<DeviceVerificationDto> devices = readDevices(scene);
        List<BoardEnvironmentVariableDto> environment = readEnvironment(scene);
        List<RuleDto> rules = readRules(scene);
        List<SpecificationDto> specs = readSpecs(scene, devices, "multi-violation");

        SmvGenerator.GenerateResult baselineModel = generator.generateWithEnvironment(
                USER_ID, devices, environment, rules, specs,
                false, 0, true, SmvGenerator.GeneratePurpose.VERIFICATION);
        assertEquals(0, baselineModel.disabledRuleCount());
        assertEquals(0, baselineModel.skippedSpecCount());

        NusmvExecutor.NusmvResult baseline = executor.execute(baselineModel.smvFile());
        assertTrue(baseline.isSuccess(), baseline::getErrorMessage);
        assertEquals(5, baseline.getSpecResults().size());
        assertEquals(2, violationCount(baseline));
        NusmvExecutor.SpecCheckResult cameraNever = baseline.getSpecResults().stream()
                .filter(result -> result.getSpecExpression().contains("camera_1.MachineState = takingphoto"))
                .filter(result -> !result.getSpecExpression().contains("trust_MachineState_takingphoto"))
                .findFirst()
                .orElseThrow();
        NusmvExecutor.SpecCheckResult untrustedCamera = baseline.getSpecResults().stream()
                .filter(result -> result.getSpecExpression().contains("trust_MachineState_takingphoto"))
                .findFirst()
                .orElseThrow();
        assertFalse(cameraNever.isPassed(), "The camera never-taking-photo property must be violated");
        assertFalse(untrustedCamera.isPassed(), "The untrusted-source camera property must be violated");
        assertNotNull(cameraNever.getCounterexample());
        assertNotNull(untrustedCamera.getCounterexample());

        SmvTraceParser traceParser = new SmvTraceParser();
        List<TraceStateDto> cameraViolationStates = traceParser.parseCounterexampleStates(
                cameraNever.getCounterexample(), baselineModel.deviceSmvMap(), rules);
        assertTrue(cameraViolationStates.size() >= 2);
        assertTrue(hasDeviceState(cameraViolationStates, "camera_1", "takingphoto"));

        SmvGenerator.GenerateResult simulationModel = generator.generateWithEnvironment(
                USER_ID, devices, environment, rules, specs,
                false, 0, true, SmvGenerator.GeneratePurpose.SIMULATION);
        NusmvExecutor.SimulationOutput simulation =
                executor.executeInteractiveSimulation(simulationModel.smvFile(), 6);
        assertTrue(simulation.isSuccess(), simulation::getErrorMessage);
        List<TraceStateDto> simulationStates = traceParser.parseCounterexampleStates(
                simulation.getTraceText(), simulationModel.deviceSmvMap(), rules);
        assertTrue(hasDeviceState(simulationStates, "camera_1", "takingphoto"));
        assertTrue(hasDeviceState(simulationStates, "alarm_1", "siren"));
        assertTrue(hasDeviceState(simulationStates, "light_1", "on"));

        FixConfig fixConfig = new FixConfig();
        fixConfig.setFixTimeoutMs(120_000);
        RuleFixer fixer = new RuleFixer(
                new FaultLocalizer(),
                List.of(new RemoveRulesFixStrategy(generator, executor)),
                fixConfig);
        FixResultDto fixResult = fixer.fix(
                200L,
                specs.get(0).getId(),
                cameraViolationStates,
                rules,
                devices,
                environment,
                specs,
                baselineModel.deviceSmvMap(),
                USER_ID,
                false,
                0,
                true,
                List.of("remove"),
                10,
                Map.of());
        FixSuggestionDto removal = fixResult.getSuggestions().stream()
                .filter(suggestion -> "remove".equals(suggestion.getStrategy()))
                .filter(FixSuggestionDto::isVerified)
                .findFirst()
                .orElseThrow();
        assertEquals(List.of(0), removal.getRemovedRuleIndices());
        assertEquals(List.of("When an untrusted hall motion signal is active, take a camera photo"),
                removal.getRemovedRuleDescriptions());

        List<RuleDto> repairedRules = new ArrayList<>(rules.subList(1, rules.size()));
        SmvGenerator.GenerateResult repairedModel = generator.generateWithEnvironment(
                USER_ID, devices, environment, repairedRules, specs,
                false, 0, true, SmvGenerator.GeneratePurpose.VERIFICATION);
        NusmvExecutor.NusmvResult repaired = executor.execute(repairedModel.smvFile());
        assertTrue(repaired.isSuccess(), repaired::getErrorMessage);
        assertEquals(5, repaired.getSpecResults().size());
        assertFalse(repaired.hasAnyViolation(),
                "Removing the root camera automation must satisfy all five specifications");
    }

    @Test
    void additionalDefaultTemplateScenes_areImportableAnimatableAndSemanticallyStable() throws Exception {
        String nusmvPath = resolveNusmvPath();
        Assumptions.assumeTrue(nusmvPath != null && Files.exists(Path.of(nusmvPath)),
                "NuSMV executable is required for the default-scene regression");

        ObjectMapper objectMapper = new ObjectMapper();
        SmvTraceParser traceParser = new SmvTraceParser();

        for (AdditionalScenarioExpectation expectation : ADDITIONAL_SCENARIOS) {
            JsonNode scene = objectMapper.readTree(Files.readString(expectation.path()));
            assertEquals("iot-verify.board-scene", scene.path("schema").asText(), expectation.name());
            assertEquals(4, scene.path("version").asInt(), expectation.name());
            assertEquals(expectation.deviceCount(), scene.path("devices").size(), expectation.name());
            assertEquals(expectation.environmentCount(), scene.path("environmentVariables").size(),
                    expectation.name());
            assertEquals(expectation.ruleCount(), scene.path("rules").size(), expectation.name());
            assertEquals(expectation.specCount(), scene.path("specs").size(), expectation.name());

            SmvGenerator generator = buildGenerator(objectMapper, scene);
            NusmvExecutor executor = buildExecutor(nusmvPath);
            List<DeviceVerificationDto> devices = readDevices(scene);
            List<BoardEnvironmentVariableDto> environment = readEnvironment(scene);
            List<RuleDto> rules = readRules(scene);
            List<SpecificationDto> specs = readSpecs(scene, devices, expectation.name());

            SmvGenerator.GenerateResult baselineModel = generator.generateWithEnvironment(
                    USER_ID, devices, environment, rules, specs,
                    false, 0, true, SmvGenerator.GeneratePurpose.VERIFICATION);
            assertEquals(0, baselineModel.disabledRuleCount(), expectation.name());
            assertEquals(0, baselineModel.skippedSpecCount(), expectation.name());
            NusmvExecutor.NusmvResult baseline = executor.execute(baselineModel.smvFile());
            assertTrue(baseline.isSuccess(), baseline::getErrorMessage);
            assertEquals(expectation.specCount(), baseline.getSpecResults().size(), expectation.name());
            assertEquals(expectation.baselineViolationCount(), violationCount(baseline), expectation.name());

            SmvGenerator.GenerateResult simulationModel = generator.generateWithEnvironment(
                    USER_ID, devices, environment, rules, specs,
                    false, 0, true, SmvGenerator.GeneratePurpose.SIMULATION);
            NusmvExecutor.SimulationOutput simulation =
                    executor.executeInteractiveSimulation(simulationModel.smvFile(), 6);
            assertTrue(simulation.isSuccess(), simulation::getErrorMessage);
            List<TraceStateDto> simulationStates = traceParser.parseCounterexampleStates(
                    simulation.getTraceText(), simulationModel.deviceSmvMap(), rules);
            assertTrue(simulationStates.size() >= 2, expectation.name() + " must be animatable");
            assertTrue(hasDeviceState(
                            simulationStates,
                            expectation.simulationDeviceId(),
                            expectation.simulationState()),
                    expectation.name() + " must expose its main automation state");

            SmvGenerator.GenerateResult attackedModel = generator.generateWithEnvironment(
                    USER_ID, devices, environment, rules, specs,
                    true, 1, true, SmvGenerator.GeneratePurpose.VERIFICATION);
            assertEquals(0, attackedModel.disabledRuleCount(), expectation.name());
            assertEquals(0, attackedModel.skippedSpecCount(), expectation.name());
            NusmvExecutor.NusmvResult attacked = executor.execute(attackedModel.smvFile());
            assertTrue(attacked.isSuccess(), attacked::getErrorMessage);
            assertEquals(expectation.attackViolationCount(), violationCount(attacked), expectation.name());

            if (expectation.removedRuleDescription() != null) {
                FixSuggestionDto removal = findVerifiedRemoval(
                        expectation,
                        baseline,
                        baselineModel,
                        traceParser,
                        generator,
                        executor,
                        rules,
                        devices,
                        environment,
                        specs);
                assertEquals(List.of(expectation.removedRuleDescription()),
                        removal.getRemovedRuleDescriptions(), expectation.name());

                Set<Integer> removedIndices = new HashSet<>(removal.getRemovedRuleIndices());
                List<RuleDto> repairedRules = new ArrayList<>();
                for (int index = 0; index < rules.size(); index++) {
                    if (!removedIndices.contains(index)) {
                        repairedRules.add(rules.get(index));
                    }
                }
                assertEquals(expectation.repairedRuleCount(), repairedRules.size(), expectation.name());

                SmvGenerator.GenerateResult repairedModel = generator.generateWithEnvironment(
                        USER_ID, devices, environment, repairedRules, specs,
                        false, 0, true, SmvGenerator.GeneratePurpose.VERIFICATION);
                NusmvExecutor.NusmvResult repaired = executor.execute(repairedModel.smvFile());
                assertTrue(repaired.isSuccess(), repaired::getErrorMessage);
                assertFalse(repaired.hasAnyViolation(),
                        expectation.name() + " verified removal must satisfy every emitted specification");
            }
        }
    }

    private FixSuggestionDto findVerifiedRemoval(
            AdditionalScenarioExpectation expectation,
            NusmvExecutor.NusmvResult baseline,
            SmvGenerator.GenerateResult baselineModel,
            SmvTraceParser traceParser,
            SmvGenerator generator,
            NusmvExecutor executor,
            List<RuleDto> rules,
            List<DeviceVerificationDto> devices,
            List<BoardEnvironmentVariableDto> environment,
            List<SpecificationDto> specs) {
        FixConfig fixConfig = new FixConfig();
        fixConfig.setFixTimeoutMs(120_000);
        RuleFixer fixer = new RuleFixer(
                new FaultLocalizer(),
                List.of(new RemoveRulesFixStrategy(generator, executor)),
                fixConfig);

        for (int index = 0; index < baseline.getSpecResults().size(); index++) {
            NusmvExecutor.SpecCheckResult result = baseline.getSpecResults().get(index);
            if (result.isPassed() || result.getCounterexample() == null) {
                continue;
            }
            List<TraceStateDto> states = traceParser.parseCounterexampleStates(
                    result.getCounterexample(), baselineModel.deviceSmvMap(), rules);
            FixResultDto fixResult = fixer.fix(
                    100L + index,
                    specs.get(index).getId(),
                    states,
                    rules,
                    devices,
                    environment,
                    specs,
                    baselineModel.deviceSmvMap(),
                    USER_ID,
                    false,
                    0,
                    true,
                    List.of("remove"),
                    10,
                    Map.of());
            Optional<FixSuggestionDto> removal = fixResult.getSuggestions().stream()
                    .filter(suggestion -> "remove".equals(suggestion.getStrategy()))
                    .filter(FixSuggestionDto::isVerified)
                    .filter(suggestion -> suggestion.getRemovedRuleDescriptions()
                            .contains(expectation.removedRuleDescription()))
                    .findFirst();
            if (removal.isPresent()) {
                return removal.get();
            }
        }
        throw new AssertionError(expectation.name() + " did not produce the expected verified removal");
    }

    private long violationCount(NusmvExecutor.NusmvResult result) {
        return result.getSpecResults().stream().filter(spec -> !spec.isPassed()).count();
    }

    private SmvGenerator buildGenerator(ObjectMapper objectMapper, JsonNode scene) throws Exception {
        Map<String, String> manifests = new java.util.LinkedHashMap<>();
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

    private NusmvExecutor buildExecutor(String nusmvPath) {
        NusmvConfig config = new NusmvConfig();
        config.setPath(nusmvPath);
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
        List<BoardEnvironmentVariableDto> environment = new ArrayList<>();
        for (JsonNode row : scene.path("environmentVariables")) {
            environment.add(new BoardEnvironmentVariableDto(
                    row.path("name").asText(),
                    row.path("value").asText(),
                    row.path("trust").asText(),
                    row.path("privacy").asText()));
        }
        return environment;
    }

    private List<RuleDto> readRules(JsonNode scene) {
        List<RuleDto> rules = new ArrayList<>();
        int index = 0;
        for (JsonNode row : scene.path("rules")) {
            List<RuleDto.Condition> conditions = new ArrayList<>();
            for (JsonNode source : row.path("sources")) {
                conditions.add(RuleDto.Condition.builder()
                        .deviceName(source.path("fromId").asText())
                        .attribute(source.path("fromApi").asText())
                        .targetType(source.path("itemType").asText())
                        .relation(textOrNull(source, "relation"))
                        .value(textOrNull(source, "value"))
                        .build());
            }
            RuleDto.Command command = RuleDto.Command.builder()
                    .deviceName(row.path("toId").asText())
                    .action(row.path("toApi").asText())
                    .contentDevice(textOrNull(row, "contentDevice"))
                    .content(textOrNull(row, "content"))
                    .build();
            rules.add(RuleDto.builder()
                    .id((long) ++index)
                    .ruleString(row.path("name").asText())
                    .conditions(conditions)
                    .command(command)
                    .build());
        }
        return rules;
    }

    private List<SpecificationDto> readSpecs(
            JsonNode scene,
            List<DeviceVerificationDto> devices,
            String idPrefix) {
        Map<String, String> labelsById = devices.stream().collect(java.util.stream.Collectors.toMap(
                DeviceVerificationDto::getVarName,
                DeviceVerificationDto::getDeviceLabel));
        List<SpecificationDto> specs = new ArrayList<>();
        int index = 0;
        for (JsonNode row : scene.path("specs")) {
            SpecificationDto spec = new SpecificationDto();
            spec.setId(idPrefix + "-spec-" + (index + 1));
            spec.setTemplateId(row.path("templateId").asText());
            spec.setTemplateLabel("Scene specification " + (index + 1));
            spec.setAConditions(readSpecConditions(row.path("aConditions"), "a", labelsById));
            spec.setIfConditions(readSpecConditions(row.path("ifConditions"), "if", labelsById));
            spec.setThenConditions(readSpecConditions(row.path("thenConditions"), "then", labelsById));
            spec.setDevices(List.of());
            specs.add(spec);
            index++;
        }
        return specs;
    }

    private List<SpecConditionDto> readSpecConditions(
            JsonNode rows, String side, Map<String, String> labelsById) {
        List<SpecConditionDto> conditions = new ArrayList<>();
        int index = 0;
        for (JsonNode row : rows) {
            SpecConditionDto condition = new SpecConditionDto();
            condition.setId(side + "-" + ++index);
            condition.setSide(side);
            condition.setDeviceId(row.path("deviceId").asText());
            condition.setDeviceLabel(labelsById.get(condition.getDeviceId()));
            condition.setTargetType(row.path("targetType").asText());
            condition.setKey(row.path("key").asText());
            condition.setPropertyScope(textOrNull(row, "propertyScope"));
            condition.setRelation(row.path("relation").asText());
            condition.setValue(row.path("value").asText());
            conditions.add(condition);
        }
        return conditions;
    }

    private List<VariableStateDto> readVariables(JsonNode rows) {
        List<VariableStateDto> variables = new ArrayList<>();
        if (!rows.isArray()) {
            return variables;
        }
        for (JsonNode row : rows) {
            variables.add(new VariableStateDto(
                    row.path("name").asText(),
                    row.path("value").asText(),
                    textOrNull(row, "trust")));
        }
        return variables;
    }

    private List<PrivacyStateDto> readPrivacies(JsonNode rows) {
        List<PrivacyStateDto> privacies = new ArrayList<>();
        if (!rows.isArray()) {
            return privacies;
        }
        for (JsonNode row : rows) {
            privacies.add(new PrivacyStateDto(
                    row.path("name").asText(),
                    row.path("privacy").asText()));
        }
        return privacies;
    }

    private String textOrNull(JsonNode row, String field) {
        JsonNode value = row.get(field);
        return value == null || value.isNull() || value.asText().isBlank() ? null : value.asText();
    }

    private boolean hasDeviceState(List<TraceStateDto> states, String deviceId, String expectedState) {
        return states.stream()
                .flatMap(state -> state.getDevices().stream())
                .anyMatch(device -> deviceId.equals(device.getDeviceId())
                        && expectedState.equals(device.getState()));
    }

    private static String resolveNusmvPath() {
        String env = System.getenv("NUSMV_PATH");
        if (env != null && !env.isBlank()) {
            return env;
        }
        Path bundled = Path.of("D:/NuSMV/NuSMV-2.7.1-win64/NuSMV-2.7.1-win64/bin/NuSMV.exe");
        return Files.exists(bundled) ? bundled.toString() : "NuSMV";
    }

    private record AdditionalScenarioExpectation(
            String name,
            Path path,
            int deviceCount,
            int environmentCount,
            int ruleCount,
            int specCount,
            int baselineViolationCount,
            int attackViolationCount,
            String simulationDeviceId,
            String simulationState,
            String removedRuleDescription,
            int repairedRuleCount) {
    }
}
