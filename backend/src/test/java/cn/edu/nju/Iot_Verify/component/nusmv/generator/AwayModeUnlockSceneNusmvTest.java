package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.executor.NusmvExecutor;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.RuleFixer;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.localize.FaultLocalizer;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy.ConditionAdjustStrategy;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy.FixStrategyApplier;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy.ParameterAdjustStrategy;
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
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
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
import static org.junit.jupiter.api.Assertions.assertTrue;
import static org.mockito.ArgumentMatchers.anyLong;
import static org.mockito.ArgumentMatchers.anyString;
import static org.mockito.Mockito.mock;
import static org.mockito.Mockito.when;

/** Temporary demo-scene probe for candidate B ("nobody home" security scene). */
class AwayModeUnlockSceneNusmvTest {

    private static final long USER_ID = 1L;
    private static final Path SCENE_PATH =
            Path.of("..", "docs", "examples", "default-away-mode-unlock-scene.json");

    /**
     * Pins the demo runbook's published numbers (docs/guides/away-mode-unlock-demo.md).
     * The presentation claims a specific baseline verdict, a specific blamed rule, and a
     * non-destructive repair that survives forward verification; if any of those change,
     * the runbook is wrong and this test must fail rather than the demo failing live.
     */
    @Test
    void awayModeUnlockScene_violatesUnlockSafetyAndIsRepairedByConditionStrategy() throws Exception {
        String nusmvPath = resolveNusmvPath();
        Assumptions.assumeTrue(nusmvPath != null && Files.exists(Path.of(nusmvPath)),
                "NuSMV executable is required for this demo-scene regression test");

        ObjectMapper objectMapper = new ObjectMapper();
        JsonNode scene = objectMapper.readTree(Files.readString(SCENE_PATH));
        assertEquals("iot-verify.board-scene", scene.path("schema").asText());
        assertEquals(4, scene.path("version").asInt());
        assertEquals(5, scene.path("devices").size());
        assertEquals(3, scene.path("rules").size());
        assertEquals(6, scene.path("specs").size());
        SmvGenerator generator = buildGenerator(objectMapper, scene);
        NusmvExecutor executor = buildExecutor(nusmvPath);
        List<DeviceVerificationDto> devices = readDevices(scene);
        List<BoardEnvironmentVariableDto> environment = readEnvironment(scene);
        List<RuleDto> rules = readRules(scene);
        List<SpecificationDto> specs = readSpecs(scene, devices, "candidateB");

        SmvGenerator.GenerateResult baselineModel = generator.generateWithEnvironment(
                USER_ID, devices, environment, rules, specs,
                AttackScenarioDto.none(), true, SmvGenerator.GeneratePurpose.VERIFICATION);
        assertEquals(0, baselineModel.disabledRuleCount(), "demo scene must not disable rules");
        assertEquals(0, baselineModel.skippedSpecCount(), "demo scene must emit all five specs");

        NusmvExecutor.NusmvResult baseline = executor.execute(baselineModel.smvFile());
        assertTrue(baseline.isSuccess(), baseline::getErrorMessage);
        assertEquals(specs.size(), baseline.getSpecResults().size());

        // Exactly one baseline violation: "never (car away & front door unlocked)" (spec index 2).
        List<Integer> violatedIndices = new ArrayList<>();
        for (int i = 0; i < baseline.getSpecResults().size(); i++) {
            if (!baseline.getSpecResults().get(i).isPassed()) {
                violatedIndices.add(i);
            }
        }
        assertEquals(List.of(2, 3), violatedIndices,
                "runbook claims four satisfied specs and two violations sharing one root cause");

        int violatedIndex = 2;
        NusmvExecutor.SpecCheckResult violation = baseline.getSpecResults().get(violatedIndex);
        assertTrue(violation.getSpecExpression().contains("door_1.LockState = unlocked"),
                () -> "unexpected violated formula: " + violation.getSpecExpression());

        List<TraceStateDto> states = new SmvTraceParser().parseCounterexampleStates(
                violation.getCounterexample(), baselineModel.deviceSmvMap(), rules);
        assertEquals(3, states.size(), "runbook walks a three-state counterexample");

        FixResultDto fixResult = allStrategyFixer(generator, executor, 240_000).fix(
                901L, specs.get(violatedIndex).getId(), states, rules, devices, environment, specs,
                baselineModel.deviceSmvMap(), USER_ID, AttackScenarioDto.none(), true,
                List.of("parameter", "condition", "remove"), 20, Map.of());
        assertTrue(fixResult.isFixable(), () -> "expected a repairable violation: " + fixResult.getSummary());

        // Localization lists every rule that fired in the trace, so all three are candidates here
        // (the porch-light rule shares the convenience rule's trigger and fires in the same step).
        // Narrowing three candidates to one repair is the strategy search's job, not localization's.
        Set<Integer> blamed = new HashSet<>();
        for (FaultRuleDto faultRule : fixResult.getFaultRules()) {
            blamed.add(faultRule.getRuleIndex());
        }
        assertTrue(blamed.contains(1), () -> "convenience-unlock rule not blamed: " + blamed);

        // Each strategy's honest outcome. Parameter tuning has no numeric inequality to move, and
        // condition tightening cannot repair this property: occupancy evolves freely, so any guard
        // that permits an unlock while someone is home is still followed by a step where they left
        // and nothing re-locks the door. Removal is therefore the only verified repair, and the
        // runbook must not promise a non-destructive one.
        Map<String, String> attemptStatus = new java.util.HashMap<>();
        fixResult.getStrategyAttempts().forEach(a -> attemptStatus.put(a.getStrategy(), a.getStatus()));
        assertEquals("SKIPPED_NO_PARAMETERIZABLE_VALUES", attemptStatus.get("parameter"),
                "this scene is enum-valued, so parameter tuning has nothing to adjust");
        assertEquals("NO_VERIFIED_SUGGESTION", attemptStatus.get("condition"));
        assertEquals("VERIFIED", attemptStatus.get("remove"));

        FixSuggestionDto removeFix = fixResult.getSuggestions().stream()
                .filter(s -> "remove".equals(s.getStrategy()))
                .findFirst()
                .orElseThrow(() -> new AssertionError("no removal suggestion offered"));
        assertTrue(removeFix.isVerified());
        assertEquals(List.of(1), removeFix.getRemovedRuleIndices(),
                "removal must target exactly the convenience-unlock rule");

        Map<String, String> deviceRefs = devices.stream().collect(
                java.util.stream.Collectors.toMap(
                        DeviceVerificationDto::getVarName, DeviceVerificationDto::getVarName));
        for (FixSuggestionDto s : fixResult.getSuggestions()) {
            List<RuleDto> repairedRules = FixStrategyApplier.apply(
                    s.getStrategy(), s, rules, baselineModel.deviceSmvMap(), deviceRefs);
            SmvGenerator.GenerateResult repairedModel = generator.generateWithEnvironment(
                    USER_ID, devices, environment, repairedRules, specs,
                    AttackScenarioDto.none(), true, SmvGenerator.GeneratePurpose.VERIFICATION);
            NusmvExecutor.NusmvResult repaired = executor.execute(repairedModel.smvFile());
            assertTrue(repaired.isSuccess(), repaired::getErrorMessage);
            assertFalse(repaired.hasAnyViolation(),
                    () -> "repair from strategy '" + s.getStrategy() + "' left a violation");
            assertEquals(specs.size(), repaired.getSpecResults().size());
            // One removal repairs both violated properties, which is the runbook's shared-root-cause claim.
            assertEquals(rules.size() - 1, repairedRules.size());
        }

        SmvGenerator.GenerateResult attackedModel = generator.generateWithEnvironment(
                USER_ID, devices, environment, rules, specs,
                AttackScenarioDto.anyUpToBudget(1), true, SmvGenerator.GeneratePurpose.VERIFICATION);
        NusmvExecutor.NusmvResult attacked = executor.execute(attackedModel.smvFile());
        assertTrue(attacked.isSuccess(), attacked::getErrorMessage);
        assertEquals(specs.size(), attacked.getSpecResults().size());

        // Act two of the demo: compromising one sensor makes the untrusted-label safety
        // property (template 7, index 3) fail, while the privacy property (index 4) holds.
        assertFalse(attacked.getSpecResults().get(4).isPassed(),
                "budget-one attack must expose the untrusted-source unlock");
        assertTrue(attacked.getSpecResults().get(5).isPassed(),
                "the privacy property is not affected by a budget-one attack");
        // Name the compromised device, not merely "something was compromised". Both sensors declare
        // `FalsifiableWhenCompromised`, so a bare `is_attack = TRUE` check passes no matter which one
        // the solver picks — it stayed green even with the occupancy sensor's flag turned off, which
        // is exactly the capability-gating regression this assertion has to catch. The exhaustive
        // budget-one search reports the porch motion detector: a doorstep sensor an attacker can
        // physically reach, which is also the stronger story for the walkthrough.
        String attackTrace = attacked.getSpecResults().get(4).getCounterexample();
        assertTrue(attackTrace.contains("motion_1.is_attack = TRUE"),
                () -> "expected the porch motion detector to be the compromised point: " + attackTrace);
        assertTrue(attackTrace.contains("door_1.trust_LockState_unlocked = untrusted"),
                "the unlock must carry an untrusted control-source label");
    }

    /**
     * The trap this scene was rebuilt to avoid, and the reason it declares its own
     * `Occupancy Sensor` template instead of reusing the bundled `Car`.
     *
     * <p>A device-local variable ({@code IsInside: true}) with no API writing it compiles to
     * {@code next(v) := v} — frozen for the whole run. An earlier draft keyed this scene on
     * {@code Car.location}, which made "the car is back in the garage" unreachable: the garage
     * rule was dead code, a Never property over it was vacuously satisfied, and the repair that
     * "kept" the unlock rule silently disabled it instead. All three read as a clean demo.
     *
     * <p>So assert the presented states are actually reachable. A satisfied property is only
     * evidence when the situation it forbids can arise at all.
     */
    @Test
    void awayModeUnlockScene_presentsNoVacuouslySatisfiedProperty() throws Exception {
        String nusmvPath = resolveNusmvPath();
        Assumptions.assumeTrue(nusmvPath != null && Files.exists(Path.of(nusmvPath)),
                "NuSMV executable is required for this demo-scene regression test");

        ObjectMapper objectMapper = new ObjectMapper();
        JsonNode scene = objectMapper.readTree(Files.readString(SCENE_PATH));
        SmvGenerator generator = buildGenerator(objectMapper, scene);
        NusmvExecutor executor = buildExecutor(nusmvPath);
        List<DeviceVerificationDto> devices = readDevices(scene);
        List<BoardEnvironmentVariableDto> environment = readEnvironment(scene);
        List<RuleDto> rules = readRules(scene);
        List<SpecificationDto> specs = readSpecs(scene, devices, "reachability");

        SmvGenerator.GenerateResult model = generator.generateWithEnvironment(
                USER_ID, devices, environment, rules, specs,
                AttackScenarioDto.none(), true, SmvGenerator.GeneratePurpose.VERIFICATION);

        // Each `AG !(p)` below asks "is p unreachable?", so every one of them must come back false.
        List<String> mustBeReachable = List.of(
                "a_occupancy = present",
                "a_occupancy = absent",
                "door_1.LockState = unlocked",
                "door_1.LockState = unlocked & a_occupancy = present",
                "alarm_1.AlertState = strobe",
                "light_1.SwitchState = on");

        String smv = Files.readString(model.smvFile().toPath());
        String head = smv.substring(0, smv.indexOf("-- Specifications"));
        StringBuilder probe = new StringBuilder(head).append("-- Specifications\n");
        for (String state : mustBeReachable) {
            probe.append("\tCTLSPEC AG !(").append(state).append(")\n");
        }
        // The probe must live in its own directory, not directly in the system temp dir.
        // `NusmvTempArtifactRegistry` locks the *parent directory* of the model file, so a probe written
        // straight into /tmp tries to lock all of /tmp — which fails on CI the moment any other NuSMV
        // test holds it, while passing locally where the temp dir is per-user and uncontended.
        Path probeDir = Files.createTempDirectory("away-mode-reachability");
        Path probeFile = probeDir.resolve("probe.smv");
        Files.writeString(probeFile, probe.toString());
        try {
            NusmvExecutor.NusmvResult result = executor.execute(probeFile.toFile());
            assertTrue(result.isSuccess(), result::getErrorMessage);
            assertEquals(mustBeReachable.size(), result.getSpecResults().size());
            for (int i = 0; i < mustBeReachable.size(); i++) {
                int index = i;
                assertFalse(result.getSpecResults().get(i).isPassed(),
                        () -> "state is unreachable, so any property over it is vacuous: "
                                + mustBeReachable.get(index));
            }
        } finally {
            // The executor writes its own artifacts (output, lock file) beside the model, so clear the
            // directory's contents before removing it.
            try (var entries = Files.list(probeDir)) {
                for (Path entry : entries.toList()) {
                    Files.deleteIfExists(entry);
                }
            }
            Files.deleteIfExists(probeDir);
        }
    }

    private RuleFixer allStrategyFixer(SmvGenerator generator, NusmvExecutor executor, int timeoutMs) {
        FixConfig fixConfig = new FixConfig();
        fixConfig.setFixTimeoutMs(timeoutMs);
        fixConfig.setMaxRefineAttempts(20);
        fixConfig.setMaxCandidatesPerRule(5);
        return new RuleFixer(
                new FaultLocalizer(),
                List.of(new ParameterAdjustStrategy(generator, executor, fixConfig),
                        new ConditionAdjustStrategy(generator, executor, fixConfig),
                        new RemoveRulesFixStrategy(generator, executor)),
                fixConfig);
    }

    private SmvGenerator buildGenerator(ObjectMapper objectMapper, JsonNode scene) {
        Map<String, String> manifests = new java.util.LinkedHashMap<>();
        for (JsonNode template : scene.path("templates")) {
            try {
                manifests.put(template.path("name").asText(),
                        objectMapper.writeValueAsString(template.path("manifest")));
            } catch (Exception e) {
                throw new IllegalStateException(e);
            }
        }
        SmvModelValidator modelValidator = new SmvModelValidator();
        DeviceTemplateService templateService = mock(DeviceTemplateService.class);
        when(templateService.findTemplateByName(anyLong(), anyString())).thenAnswer(invocation -> {
            String templateName = invocation.getArgument(1, String.class);
            String manifest = manifests.get(templateName);
            return manifest == null ? Optional.empty() : Optional.of(DeviceTemplatePo.builder()
                    .id(100L).userId(USER_ID).name(templateName)
                    .manifestJson(manifest).defaultTemplate(true).build());
        });
        DeviceSmvDataFactory factory = new DeviceSmvDataFactory(
                objectMapper, templateService, modelValidator,
                new DeviceTemplateSchemaValidator(objectMapper));
        return new SmvGenerator(factory, new SmvDeviceModuleBuilder(), new SmvRuleCommentWriter(),
                new SmvMainModuleBuilder(), new SmvSpecificationBuilder(), modelValidator);
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
                    row.path("name").asText(), row.path("value").asText(),
                    row.path("trust").asText(), row.path("privacy").asText()));
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
                    .build();
            rules.add(RuleDto.builder().id((long) ++index)
                    .ruleString(row.path("name").asText())
                    .conditions(conditions).command(command).build());
        }
        return rules;
    }

    private List<SpecificationDto> readSpecs(
            JsonNode scene, List<DeviceVerificationDto> devices, String idPrefix) {
        Map<String, String> labelsById = devices.stream().collect(java.util.stream.Collectors.toMap(
                DeviceVerificationDto::getVarName, DeviceVerificationDto::getDeviceLabel));
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
            variables.add(new VariableStateDto(row.path("name").asText(),
                    row.path("value").asText(), textOrNull(row, "trust")));
        }
        return variables;
    }

    private List<PrivacyStateDto> readPrivacies(JsonNode rows) {
        List<PrivacyStateDto> privacies = new ArrayList<>();
        if (!rows.isArray()) {
            return privacies;
        }
        for (JsonNode row : rows) {
            privacies.add(new PrivacyStateDto(row.path("name").asText(), row.path("privacy").asText()));
        }
        return privacies;
    }

    private String textOrNull(JsonNode row, String field) {
        JsonNode value = row.get(field);
        return value == null || value.isNull() || value.asText().isBlank() ? null : value.asText();
    }

    private static String resolveNusmvPath() {
        String env = System.getenv("NUSMV_PATH");
        if (env != null && !env.isBlank()) {
            return env;
        }
        Path bundled = Path.of("D:/NuSMV/NuSMV-2.7.1-win64/NuSMV-2.7.1-win64/bin/NuSMV.exe");
        return Files.exists(bundled) ? bundled.toString() : "NuSMV";
    }
}
