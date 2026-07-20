package cn.edu.nju.Iot_Verify.component.nusmv.fixer.strategy;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.fixer.parameterize.ParameterizationConfig;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackPointDto;
import cn.edu.nju.Iot_Verify.dto.model.AttackScenarioDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;
import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import org.junit.jupiter.api.Test;

import java.util.*;

import static org.junit.jupiter.api.Assertions.*;

class FixStrategyUtilsTest {

    @Test
    void commandFingerprint_distinguishesContentPayloadsForTheSameAction() {
        Map<String, DeviceSmvData> devices = buildDeviceMap("display", "camera", "hub");
        RuleDto showPhoto = RuleDto.builder()
                .command(RuleDto.Command.builder()
                        .deviceName("display").action("show")
                        .contentDevice("camera").content("photo").build())
                .build();
        RuleDto showLog = RuleDto.builder()
                .command(RuleDto.Command.builder()
                        .deviceName("display").action("show")
                        .contentDevice("hub").content("log").build())
                .build();

        assertNotEquals(
                FixStrategyUtils.commandFingerprint(showPhoto, devices),
                FixStrategyUtils.commandFingerprint(showLog, devices));
    }

    @Test
    void candidateRulesPersistable_usesTheBoardExactDuplicateSemantics() {
        RuleDto first = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("temperature_1").targetType("variable")
                        .attribute("temperature").relation(">=").value("36").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("heat").build())
                .build();
        RuleDto duplicateWithAlias = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("temperature_1").targetType("variable")
                        .attribute("temperature").relation("GTE").value("36").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("heat").build())
                .build();
        RuleDto distinctThreshold = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("temperature_1").targetType("variable")
                        .attribute("temperature").relation(">=").value("37").build()))
                .command(RuleDto.Command.builder().deviceName("ac_1").action("heat").build())
                .build();

        assertFalse(FixStrategyUtils.candidateRulesPersistable(List.of(first, duplicateWithAlias)));
        assertTrue(FixStrategyUtils.candidateRulesPersistable(List.of(first, distinctThreshold)));
    }

    @Test
    void preservesExactAttackSelection_requiresEverySelectedPointToRemainEffectful() {
        AttackScenarioDto exactLink = AttackScenarioDto.exactPoints(List.of(
                AttackPointDto.automationLink(7L)));

        assertTrue(FixStrategyUtils.preservesExactAttackSelection(
                exactLink, List.of(RuleDto.builder().id(7L).build()), Map.of()));
        assertFalse(FixStrategyUtils.preservesExactAttackSelection(
                exactLink, List.of(RuleDto.builder().id(8L).build()), Map.of()));
        assertFalse(FixStrategyUtils.preservesExactAttackSelection(
                exactLink, List.of(
                        RuleDto.builder().id(7L).build(),
                        RuleDto.builder().id(7L).build()), Map.of()));

        Map<String, DeviceSmvData> devices = buildDeviceMap("light_1", "sensor_1");
        RuleDto commandTarget = RuleDto.builder()
                .id(7L)
                .command(RuleDto.Command.builder().deviceName("light_1").action("on").build())
                .build();
        AttackScenarioDto exactDevice = AttackScenarioDto.exactPoints(List.of(
                AttackPointDto.device("light_1")));
        assertTrue(FixStrategyUtils.preservesExactAttackSelection(
                exactDevice, List.of(commandTarget), devices));
        assertFalse(FixStrategyUtils.preservesExactAttackSelection(
                exactDevice, List.of(), devices),
                "removing the last command to a selected target must not disable its attack variable");

        devices.get("sensor_1").getVariables().get(0).setFalsifiableWhenCompromised(true);
        assertTrue(FixStrategyUtils.preservesExactAttackSelection(
                AttackScenarioDto.exactPoints(List.of(AttackPointDto.device("sensor_1"))),
                List.of(), devices),
                "a selected falsifiable-reading device remains effectful without command rules");
    }

    // ======================== E2: expandRuleIndices ========================

    private Map<String, DeviceSmvData> buildDeviceMap(String... varNames) {
        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        for (String name : varNames) {
            DeviceSmvData smv = new DeviceSmvData();
            smv.setVarName(name);
            smv.setModuleName(name + "Module");
            smv.setModes(List.of("default"));  // single mode (generator requires modes for state)
            smv.getModeStates().put("default", new ArrayList<>(List.of("on", "off")));
            smv.setStates(List.of("on", "off"));
            DeviceManifest.InternalVariable tempVar = DeviceManifest.InternalVariable.builder()
                    .name("temperature")
                    .lowerBound(0)
                    .upperBound(100)
                    .build();
            smv.setVariables(List.of(tempVar));
            map.put(name, smv);
        }
        return map;
    }

    private Map<String, DeviceSmvData> buildEnvironmentDeviceMap(String varName, String environmentName) {
        DeviceManifest.InternalVariable env = DeviceManifest.InternalVariable.builder()
                .name(environmentName)
                .isInside(false)
                .lowerBound(0)
                .upperBound(100)
                .build();
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName(varName);
        smv.setModuleName(varName + "Module");
        smv.setModes(List.of("default"));
        smv.getModeStates().put("default", new ArrayList<>(List.of("on", "off")));
        smv.setStates(List.of("on", "off"));
        smv.setVariables(List.of(env));
        smv.getEnvVariables().put(environmentName, env);
        return Map.of(varName, smv);
    }

    private SpecificationDto buildSpec(SpecConditionDto... conditions) {
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");
        spec.setTemplateLabel("test");
        List<SpecConditionDto> list = new ArrayList<>(Arrays.asList(conditions));
        spec.setAConditions(list);
        spec.setIfConditions(new ArrayList<>());
        spec.setThenConditions(new ArrayList<>());
        return spec;
    }

    private SpecConditionDto buildSpecCond(String deviceId, String targetType, String key, String relation, String value) {
        SpecConditionDto sc = new SpecConditionDto();
        sc.setDeviceId(deviceId);
        sc.setTargetType(targetType);
        sc.setKey(key);
        sc.setRelation(relation);
        sc.setValue(value);
        return sc;
    }

    @Test
    void expandRuleIndices_includesFaultRulesAndSharedDeviceRules() {
        // rule0: conditions on deviceA; rule1: conditions on deviceA; rule2: conditions on deviceB
        RuleDto rule0 = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("deviceA").targetType("variable").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("deviceB").action("on").build())
                .build();
        RuleDto rule1 = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("deviceA").targetType("variable").attribute("temperature").relation("<").value("10").build()))
                .command(RuleDto.Command.builder().deviceName("deviceC").action("off").build())
                .build();
        RuleDto rule2 = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("deviceC").targetType("state").attribute("state").relation("=").value("on").build()))
                .command(RuleDto.Command.builder().deviceName("deviceC").action("off").build())
                .build();
        List<RuleDto> allRules = List.of(rule0, rule1, rule2);

        // faultRules: only rule0, rule2
        List<FaultRuleDto> faultRules = List.of(
                FaultRuleDto.builder().ruleIndex(0).build(),
                FaultRuleDto.builder().ruleIndex(2).build());

        // spec references deviceA → rule1 also shares deviceA → should be included
        SpecificationDto spec = buildSpec(buildSpecCond("deviceA", "variable", "temperature", ">", "25"));
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("deviceA", "deviceB", "deviceC");

        Set<Integer> result = FixStrategyUtils.expandRuleIndices(faultRules, allRules, spec, deviceMap);

        assertEquals(Set.of(0, 1, 2), result);
    }

    @Test
    void expandRuleIndices_emptySpec_returnsFaultRulesOnly() {
        RuleDto rule0 = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("deviceA").targetType("variable").attribute("temp").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("deviceB").action("on").build())
                .build();
        List<FaultRuleDto> faultRules = List.of(FaultRuleDto.builder().ruleIndex(0).build());
        SpecificationDto spec = buildSpec(); // empty conditions
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("deviceA");

        Set<Integer> result = FixStrategyUtils.expandRuleIndices(faultRules, List.of(rule0), spec, deviceMap);

        assertEquals(Set.of(0), result);
    }

    @Test
    void expandRuleIndices_commandDeviceMatch() {
        RuleDto rule0 = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("deviceB").targetType("variable").attribute("temp").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("deviceB").action("on").build())
                .build();
        // rule1 has no condition on deviceA, but command targets deviceA
        RuleDto rule1 = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("deviceB").targetType("variable").attribute("temp").relation("<").value("10").build()))
                .command(RuleDto.Command.builder().deviceName("deviceA").action("on").build())
                .build();
        List<RuleDto> allRules = List.of(rule0, rule1);

        List<FaultRuleDto> faultRules = List.of(FaultRuleDto.builder().ruleIndex(0).build());
        SpecificationDto spec = buildSpec(buildSpecCond("deviceA", "variable", "temp", ">", "25"));
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("deviceA", "deviceB");

        Set<Integer> result = FixStrategyUtils.expandRuleIndices(faultRules, allRules, spec, deviceMap);

        assertTrue(result.contains(1), "rule1 should be included via command.deviceName match");
    }

    @Test
    void expandRuleIndices_includesRulesSharingEnvironmentalDomain() {
        Map<String, DeviceSmvData> deviceMap = new LinkedHashMap<>(buildDeviceMap(
                "heater", "sensor", "fan"));
        DeviceManifest.InternalVariable temperature = DeviceManifest.InternalVariable.builder()
                .name("temperature").isInside(false).lowerBound(0).upperBound(100).build();
        deviceMap.get("heater").setImpactedVariables(List.of("temperature"));
        deviceMap.get("heater").getImpactedEnvironmentVariables().put("temperature", temperature);
        deviceMap.get("sensor").getEnvVariables().put("temperature", temperature);

        RuleDto sharedDomainRule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor").targetType("variable").attribute("temperature")
                        .relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("fan").action("on").build())
                .build();
        SpecificationDto spec = buildSpec(
                buildSpecCond("heater", "state", null, "=", "on"));

        Set<Integer> result = FixStrategyUtils.expandRuleIndices(
                null, List.of(sharedDomainRule), spec, deviceMap);

        assertEquals(Set.of(0), result);
    }

    @Test
    void expandRuleIndices_ignoresSpecDeviceLabelWhenDeviceIdIsUnknown() {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("LivingRoomAC").targetType("variable").attribute("temperature").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("LivingRoomAC").action("on").build())
                .build();
        SpecConditionDto specCond = buildSpecCond("node-1", "variable", "temperature", ">", "25");
        specCond.setDeviceLabel("LivingRoomAC");
        SpecificationDto spec = buildSpec(specCond);
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("LivingRoomAC");

        Set<Integer> result = FixStrategyUtils.expandRuleIndices(null, List.of(rule), spec, deviceMap);

        assertTrue(result.isEmpty(),
                "deviceLabel is display-only; scope expansion must not resolve unknown deviceId through label fallback");
    }

    @Test
    void expandRuleIndices_nullFaultRules_scansSharedDeviceOnly() {
        RuleDto rule0 = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("deviceA").targetType("variable").attribute("temp").relation(">").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("deviceB").action("on").build())
                .build();
        SpecificationDto spec = buildSpec(buildSpecCond("deviceA", "variable", "temp", ">", "25"));
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("deviceA", "deviceB");

        Set<Integer> result = FixStrategyUtils.expandRuleIndices(null, List.of(rule0), spec, deviceMap);

        assertEquals(Set.of(0), result);
    }

    @Test
    void expandRuleIndices_outOfBoundsFaultRuleIndex_skipped() {
        List<FaultRuleDto> faultRules = List.of(FaultRuleDto.builder().ruleIndex(99).build());
        SpecificationDto spec = buildSpec();

        Set<Integer> result = FixStrategyUtils.expandRuleIndices(faultRules, List.of(), spec, Map.of());

        assertTrue(result.isEmpty());
    }

    // ======================== E1: extractCandidateConditions ========================

    @Test
    void extractCandidateConditions_stateMapping() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("thermo");

        RuleDto rule = RuleDto.builder().conditions(new ArrayList<>()).build();
        SpecificationDto spec = buildSpec(
                buildSpecCond("thermo", "state", "on", "=", "on"));

        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                spec, rule, deviceMap, 5);

        assertEquals(1, candidates.size());
        assertEquals("state", candidates.get(0).getAttribute());
        assertEquals("on", candidates.get(0).getValue());
    }

    @Test
    void extractCandidateConditions_variableMapping() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto rule = RuleDto.builder().conditions(new ArrayList<>()).build();
        SpecificationDto spec = buildSpec(
                buildSpecCond("sensor", "variable", "temperature", ">", "30"));

        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                spec, rule, deviceMap, 5);

        assertEquals(1, candidates.size());
        assertEquals("temperature", candidates.get(0).getAttribute());
        assertEquals(">", candidates.get(0).getRelation());
    }

    @Test
    void candidateConditionValueInfo_exposesDiscreteVariableDomainForFreeValue() {
        DeviceManifest.InternalVariable occupied = DeviceManifest.InternalVariable.builder()
                .name("occupied")
                .values(List.of("TRUE", "FALSE"))
                .build();
        DeviceSmvData sensor = new DeviceSmvData();
        sensor.setVarName("occupancy_1");
        sensor.setVariables(List.of(occupied));

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("occupancy_1")
                .targetType("variable")
                .attribute("occupied")
                .relation("=")
                .value("FALSE")
                .build();

        ParameterizationConfig.ConditionValueInfo info =
                FixStrategyUtils.candidateConditionValueInfo(
                        candidate, Map.of("occupancy_1", sensor), "condition_value_r0_c1");

        assertNotNull(info);
        assertEquals("condition_value_r0_c1", info.getFrozenVarName());
        assertEquals(List.of("TRUE", "FALSE"), info.getValues());
        assertNull(info.getLowerBound());
        assertNull(info.getUpperBound());
    }

    @Test
    void candidateConditionValueInfo_exposesNumericVariableBounds() {
        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor")
                .targetType("variable")
                .attribute("temperature")
                .relation("<=")
                .value("18")
                .build();

        ParameterizationConfig.ConditionValueInfo info =
                FixStrategyUtils.candidateConditionValueInfo(
                        candidate, buildDeviceMap("sensor"), "condition_value_r0_c1");

        assertNotNull(info);
        assertEquals(0, info.getLowerBound());
        assertEquals(100, info.getUpperBound());
        assertTrue(info.getValues().isEmpty());
    }

    @Test
    void extractCandidateConditions_modeMapping() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto rule = RuleDto.builder().conditions(new ArrayList<>()).build();
        SpecificationDto spec = buildSpec(
                buildSpecCond("sensor", "mode", "default", "=", "on"));

        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                spec, rule, deviceMap, 5);

        assertEquals(1, candidates.size());
        assertEquals("default", candidates.get(0).getAttribute());
        assertEquals("=", candidates.get(0).getRelation());
        assertEquals("on", candidates.get(0).getValue());
    }

    @Test
    void extractCandidateConditions_skipsCommandPostconditionButKeepsRealPrecondition() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("camera");
        DeviceSmvData camera = deviceMap.get("camera");
        camera.setModes(List.of("MachineState"));
        camera.getModeStates().clear();
        camera.getModeStates().put("MachineState", new ArrayList<>(List.of("off", "on", "takingphoto")));
        camera.setStates(List.of("off", "on", "takingphoto"));
        camera.setManifest(DeviceManifest.builder()
                .name("Camera")
                .apis(List.of(DeviceManifest.API.builder()
                        .name("take photo")
                        .startState("on")
                        .endState("taking photo")
                        .signal(true)
                        .build()))
                .build());

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("camera")
                        .targetType("state")
                        .attribute("state")
                        .relation("=")
                        .value("on")
                        .build()))
                .command(RuleDto.Command.builder().deviceName("camera").action("take photo").build())
                .build();

        List<RuleDto.Condition> postcondition = FixStrategyUtils.extractCandidateConditions(
                buildSpec(buildSpecCond("camera", "state", null, "=", "taking photo")),
                rule, deviceMap, 5);
        assertTrue(postcondition.isEmpty(),
                "a command's own EndState must not become the rule's trigger condition");

        List<RuleDto.Condition> realPrecondition = FixStrategyUtils.extractCandidateConditions(
                buildSpec(buildSpecCond("camera", "state", null, "=", "on")),
                RuleDto.builder()
                        .conditions(new ArrayList<>())
                        .command(RuleDto.Command.builder().deviceName("camera").action("take photo").build())
                        .build(),
                deviceMap, 5);
        assertEquals(1, realPrecondition.size(),
                "a state that precedes the command remains a valid condition candidate");

        RuleDto commandOnly = RuleDto.builder()
                .conditions(new ArrayList<>())
                .command(RuleDto.Command.builder().deviceName("camera").action("take photo").build())
                .build();
        List<RuleDto.Condition> contradictoryPrecondition = FixStrategyUtils.extractCandidateConditions(
                buildSpec(buildSpecCond("camera", "state", null, "=", "off")),
                commandOnly, deviceMap, 5);
        assertTrue(contradictoryPrecondition.isEmpty(),
                "a condition that contradicts the API StartState would make the command unreachable");

        List<RuleDto.Condition> contradictoryNegativePrecondition = FixStrategyUtils.extractCandidateConditions(
                buildSpec(buildSpecCond("camera", "state", null, "!=", "on")),
                commandOnly, deviceMap, 5);
        assertTrue(contradictoryNegativePrecondition.isEmpty(),
                "negative conditions that are false in the API StartState are also unreachable");

        List<RuleDto.Condition> compatibleNegativePrecondition = FixStrategyUtils.extractCandidateConditions(
                buildSpec(buildSpecCond("camera", "state", null, "!=", "taking photo")),
                commandOnly, deviceMap, 5);
        assertEquals(1, compatibleNegativePrecondition.size(),
                "a negative guard that is true in the API StartState remains eligible");

        camera.getManifest().getApis().get(0).setStartState("_");
        List<RuleDto.Condition> wildcardStartCandidate = FixStrategyUtils.extractCandidateConditions(
                buildSpec(buildSpecCond("camera", "state", null, "=", "off")),
                commandOnly, deviceMap, 5);
        assertEquals(1, wildcardStartCandidate.size(),
                "a wildcard API StartState must not be treated as a proven contradiction");
    }

    @Test
    void extractCandidateConditions_ignoresDeviceLabelWhenSpecDeviceIdIsUnknown() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("LivingRoomAC");

        RuleDto rule = RuleDto.builder().conditions(new ArrayList<>()).build();
        SpecConditionDto cond = buildSpecCond("ac_1", "state", null, "=", "on");
        cond.setDeviceLabel("LivingRoomAC");
        SpecificationDto spec = buildSpec(cond);

        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                spec, rule, deviceMap, 5);

        assertTrue(candidates.isEmpty(),
                "deviceLabel is display-only; candidate extraction must not resolve unknown deviceId through label fallback");
    }

    @Test
    void extractCandidateConditions_supportsPositiveApiAndSkipsTrustPrivacy() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");
        deviceMap.get("sensor").setManifest(DeviceManifest.builder()
                .apis(List.of(DeviceManifest.API.builder()
                        .name("turnOn").signal(true).startState("").build()))
                .build());

        RuleDto rule = RuleDto.builder().conditions(new ArrayList<>()).build();
        SpecificationDto spec = buildSpec(
                buildSpecCond("sensor", "api", "turnOn", "=", "TRUE"),
                buildSpecCond("sensor", "trust", "mode", "=", "trusted"),
                buildSpecCond("sensor", "privacy", "mode", "=", "public"));

        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                spec, rule, deviceMap, 5);

        assertEquals(1, candidates.size());
        assertEquals("api", candidates.get(0).getTargetType());
        assertEquals("turnOn", candidates.get(0).getAttribute());
        assertNull(candidates.get(0).getRelation());
        assertNull(candidates.get(0).getValue());
    }

    @Test
    void extractCandidateConditions_maxLimit() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto rule = RuleDto.builder().conditions(new ArrayList<>()).build();
        // Distinct free-value shapes; repeated literals of one shape are intentionally deduplicated.
        List<SpecConditionDto> conds = new ArrayList<>();
        for (String relation : List.of(">", ">=", "<", "<=")) {
            conds.add(buildSpecCond("sensor", "variable", "temperature", relation, "30"));
        }
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");
        spec.setTemplateLabel("test");
        spec.setAConditions(conds);
        spec.setIfConditions(new ArrayList<>());
        spec.setThenConditions(new ArrayList<>());

        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                spec, rule, deviceMap, 3);

        assertEquals(3, candidates.size());
    }

    @Test
    void extractCandidateConditions_filtersExistingConditions() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        // Rule already has temp>30
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("sensor").targetType("variable").attribute("temperature").relation(">").value("30").build()))
                .build();
        // Spec also has temp>30
        SpecificationDto spec = buildSpec(
                buildSpecCond("sensor", "variable", "temperature", ">", "30"));

        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                spec, rule, deviceMap, 5);

        assertTrue(candidates.isEmpty(), "duplicate should be filtered");
    }

    @Test
    void extractCandidateConditions_dedup() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto rule = RuleDto.builder().conditions(new ArrayList<>()).build();
        // Same condition in aConditions and ifConditions
        SpecificationDto spec = new SpecificationDto();
        spec.setId("s1");
        spec.setTemplateId("1");
        spec.setTemplateLabel("test");
        spec.setAConditions(List.of(buildSpecCond("sensor", "variable", "temperature", ">", "30")));
        spec.setIfConditions(List.of(buildSpecCond("sensor", "variable", "temperature", ">", "30")));
        spec.setThenConditions(new ArrayList<>());

        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                spec, rule, deviceMap, 5);

        assertEquals(1, candidates.size(), "dedup should produce only 1 candidate");
    }

    @Test
    void extractCandidateConditions_deduplicatesFreeValueShapesAcrossPolicyLiterals() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");
        RuleDto rule = RuleDto.builder().conditions(new ArrayList<>()).build();
        SpecificationDto spec = buildSpec(
                buildSpecCond("sensor", "variable", "temperature", ">", "30"),
                buildSpecCond("sensor", "variable", "temperature", ">", "40"));

        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                spec, rule, deviceMap, 5);

        assertEquals(1, candidates.size(),
                "a free-Y condition shape must consume only one candidate slot");
    }

    @Test
    void extractCandidateConditions_doesNotAddFreeValueShapeAlreadyPresentInRule() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");
        RuleDto rule = RuleDto.builder().conditions(List.of(RuleDto.Condition.builder()
                .deviceName("sensor").targetType("variable").attribute("temperature")
                .relation(">").value("35").build())).build();

        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                buildSpec(buildSpecCond("sensor", "variable", "temperature", ">", "30")),
                rule, deviceMap, 5);

        assertTrue(candidates.isEmpty());
    }

    @Test
    void extractCandidateConditions_prunesCommandOutcomeFromFreeModeDomain() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("camera");
        DeviceSmvData camera = deviceMap.get("camera");
        camera.getModeStates().put("default", new ArrayList<>(List.of("off", "on", "takingphoto")));
        camera.setStates(List.of("off", "on", "takingphoto"));
        camera.setManifest(DeviceManifest.builder()
                .name("Camera")
                .apis(List.of(DeviceManifest.API.builder()
                        .name("turn on")
                        .startState("_")
                        .endState("on")
                        .signal(true)
                        .build()))
                .build());
        RuleDto rule = RuleDto.builder()
                .conditions(new ArrayList<>())
                .command(RuleDto.Command.builder().deviceName("camera").action("turn on").build())
                .build();

        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                buildSpec(buildSpecCond("camera", "mode", "default", "=", "on")),
                rule, deviceMap, 5);

        assertEquals(1, candidates.size(),
                "a single unsafe policy literal must not discard the entire free-Y candidate");
        ParameterizationConfig.ConditionValueInfo valueInfo =
                FixStrategyUtils.candidateConditionValueInfo(
                        candidates.get(0), rule, deviceMap, "condition_value_r0_c1");
        assertNotNull(valueInfo);
        assertEquals(List.of("off", "takingphoto"), valueInfo.getValues());
    }

    @Test
    void extractCandidateConditions_nullSpec_returnsEmpty() {
        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                null, RuleDto.builder().build(), Map.of(), 5);

        assertTrue(candidates.isEmpty());
    }

    // ======================== E1: validateCandidateCondition ========================

    @Test
    void validateCandidateCondition_validVariable() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("variable").attribute("temperature").relation(">").value("30").build();

        assertTrue(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    @Test
    void validateCandidateCondition_environmentVariableNamesAreLiteral() {
        Map<String, DeviceSmvData> literalPrefixed = buildEnvironmentDeviceMap("sensor", "a_temperature");
        RuleDto.Condition actualAPrefixedName = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("variable").attribute("a_temperature").relation(">").value("30").build();

        assertTrue(FixStrategyUtils.validateCandidateCondition(actualAPrefixedName, literalPrefixed),
                "a_ can be part of a real template variable name");

        Map<String, DeviceSmvData> ordinary = buildEnvironmentDeviceMap("sensor", "temperature");
        RuleDto.Condition generatedAlias = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("variable").attribute("a_temperature").relation(">").value("30").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(generatedAlias, ordinary),
                "a_temperature must not be treated as an alias for template variable temperature");
    }

    @Test
    void validateCandidateCondition_validState() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("state").attribute("state").relation("=").value("on").build();

        assertTrue(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    @Test
    void validateCandidateCondition_validMode() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("mode").attribute("default").relation("=").value("on").build();

        assertTrue(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    @Test
    void validateCandidateCondition_modeWithGreaterThan_rejected() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("mode").attribute("default").relation(">").value("on").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    @Test
    void validateCandidateCondition_modeInvalidValue_rejected() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("mode").attribute("default").relation("=").value("missing").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    @Test
    void validateCandidateCondition_invalidDevice() {
        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("nonexistent").targetType("variable").attribute("temperature").relation(">").value("30").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, Map.of()));
    }

    @Test
    void validateCandidateCondition_invalidState() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("state").attribute("state").relation("=").value("nonexistent_state").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    @Test
    void validateCandidateCondition_unknownVariable() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("variable").attribute("unknownAttr").relation(">").value("30").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    @Test
    void validateCandidateCondition_nullRelation() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("variable").attribute("temperature").relation(null).value("30").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    @Test
    void validateCandidateCondition_blankValue() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("variable").attribute("temperature").relation(">").value("  ").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    // ======================== conditionFingerprint ========================

    @Test
    void conditionFingerprint_producesConsistentResult() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition c = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("variable").attribute("temperature").relation(">").value("30").build();

        String fp1 = FixStrategyUtils.conditionFingerprint(c, deviceMap);
        String fp2 = FixStrategyUtils.conditionFingerprint(c, deviceMap);

        assertNotNull(fp1);
        assertEquals(fp1, fp2);
        assertTrue(fp1.contains("sensor"));
        assertTrue(fp1.contains("temperature"));
    }

    @Test
    void conditionFingerprint_nullDevice_returnsNull() {
        RuleDto.Condition c = RuleDto.Condition.builder()
                .deviceName("nonexistent").targetType("variable").attribute("temp").relation(">").value("30").build();

        assertNull(FixStrategyUtils.conditionFingerprint(c, Map.of()));
    }

    // ======================== HIGH 1: state relation + IN/NOT_IN ========================

    @Test
    void validateCandidateCondition_stateWithGreaterThan_rejected() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        // state conditions only allow = != in not_in — ">" should be rejected
        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("state").attribute("state").relation(">").value("on").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap),
                "state with > relation must be rejected (SmvMainModuleBuilder only allows = != in not_in)");
    }

    @Test
    void validateCandidateCondition_stateWithLessThan_rejected() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("state").attribute("state").relation("<").value("on").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    @Test
    void validateCandidateCondition_stateInValidValues_accepted() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        // IN with both values valid
        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("state").attribute("state").relation("in").value("on,off").build();

        assertTrue(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    @Test
    void validateCandidateCondition_stateInWithInvalidValue_rejected() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        // IN with one invalid value
        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("state").attribute("state").relation("in").value("on,invalid_state").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap),
                "IN with any invalid state must be rejected");
    }

    @Test
    void validateCandidateCondition_stateNotInValidValues_accepted() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("state").attribute("state").relation("not in").value("on").build();

        assertTrue(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    @Test
    void validateCandidateCondition_stateNotEq_accepted() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("state").attribute("state").relation("!=").value("on").build();

        assertTrue(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    // ======================== MEDIUM: multi-mode state IN/NOT_IN splitting ========================

    /**
     * Build a multi-mode device (modes.size > 1) where ; is part of tuple values.
     * E.g. HVAC with modes ["power", "fan"] → states like "cool;high", "heat;low".
     */
    private Map<String, DeviceSmvData> buildMultiModeDeviceMap(String varName) {
        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName(varName);
        smv.setModuleName(varName + "Module");
        smv.setModes(List.of("power", "fan"));  // 2 modes → multi-mode
        // modeStates: per-mode valid state values (what resolveStateTupleCandidate checks)
        smv.getModeStates().put("power", new ArrayList<>(List.of("cool", "heat", "off")));
        smv.getModeStates().put("fan", new ArrayList<>(List.of("high", "low", "off")));
        // flat states list (what extractStatesAndTrust produces via sanitizeSmvToken)
        smv.setStates(List.of("cool_high", "cool_low", "heat_high", "heat_low", "off_off"));
        smv.setVariables(List.of());
        map.put(varName, smv);
        return map;
    }

    @Test
    void validateCandidateCondition_multiModeStateIn_semicolonPreserved() {
        // Multi-mode device: "cool;high" is a single tuple value, NOT two values
        Map<String, DeviceSmvData> deviceMap = buildMultiModeDeviceMap("hvac");

        // "cool;high,heat;low" should split into ["cool;high", "heat;low"] by [,|] only
        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("hvac").targetType("state").attribute("state").relation("in").value("cool;high,heat;low").build();

        // cleanStateName("cool;high") → "cool_high" which is in states
        assertTrue(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap),
                "Multi-mode IN must split by [,|] only, preserving ; within tuples");
    }

    @Test
    void validateCandidateCondition_multiModeStateNotIn_semicolonPreserved() {
        Map<String, DeviceSmvData> deviceMap = buildMultiModeDeviceMap("hvac");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("hvac").targetType("state").attribute("state").relation("not in").value("off;off").build();

        assertTrue(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap),
                "Multi-mode NOT_IN must preserve ; within tuples");
    }

    @Test
    void validateCandidateCondition_singleModeStateIn_semicolonSplits() {
        // Single-mode device: ; is a regular delimiter
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        // "on;off" should split into ["on", "off"] for single-mode device
        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("state").attribute("state").relation("in").value("on;off").build();

        assertTrue(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap),
                "Single-mode IN should split ; as delimiter");
    }

    @Test
    void validateCandidateCondition_multiModeSingleValue_uniqueMode_accepted() {
        // "cool" exists only in mode "power" → exactly one match → valid
        Map<String, DeviceSmvData> deviceMap = buildMultiModeDeviceMap("hvac");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("hvac").targetType("state").attribute("state").relation("=").value("cool").build();

        assertTrue(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap),
                "Single value on multi-mode device should be valid when exactly one mode matches");
    }

    @Test
    void validateCandidateCondition_multiModeSingleValue_ambiguous_rejected() {
        // "off" exists in BOTH modes "power" and "fan" → ambiguous → rejected
        Map<String, DeviceSmvData> deviceMap = buildMultiModeDeviceMap("hvac");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("hvac").targetType("state").attribute("state").relation("=").value("off").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap),
                "Single value matching multiple modes must be rejected (ambiguous)");
    }

    @Test
    void validateCandidateCondition_multiModeSingleValue_notFound_rejected() {
        Map<String, DeviceSmvData> deviceMap = buildMultiModeDeviceMap("hvac");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("hvac").targetType("state").attribute("state").relation("=").value("turbo").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap),
                "Single value not in any mode must be rejected");
    }

    @Test
    void validateCandidateCondition_allWildcardTuple_rejected() {
        // ";" on 2-mode device → all segments empty → all-wildcard → generator returns null
        Map<String, DeviceSmvData> deviceMap = buildMultiModeDeviceMap("hvac");

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("hvac").targetType("state").attribute("state").relation("=").value(";").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap),
                "All-wildcard tuple must be rejected (resolveStateTupleCandidate:697 returns null)");
    }

    @Test
    void validateCandidateCondition_underscoreWildcardTuple_acceptedWhenAnotherSegmentIsConcrete() {
        Map<String, DeviceSmvData> deviceMap = buildMultiModeDeviceMap("hvac");
        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("hvac").targetType("state").attribute("state")
                .relation("=").value("cool;_").build();

        assertTrue(FixStrategyUtils.validateCandidateCondition(candidate, deviceMap));
    }

    @Test
    void validateCandidateCondition_noModes_rejected() {
        // Device with no modes → state condition invalid (SmvMainModuleBuilder:591)
        Map<String, DeviceSmvData> map = new LinkedHashMap<>();
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName("nomode");
        smv.setModuleName("noModeModule");
        smv.setModes(List.of());  // empty modes
        smv.setStates(List.of("on", "off"));
        smv.setVariables(List.of());
        map.put("nomode", smv);

        RuleDto.Condition candidate = RuleDto.Condition.builder()
                .deviceName("nomode").targetType("state").attribute("state").relation("=").value("on").build();

        assertFalse(FixStrategyUtils.validateCandidateCondition(candidate, map),
                "State condition on no-mode device must be rejected (generator requires modes)");
    }

    // ======================== conditionFingerprint: multi-mode mode-aware ========================

    @Test
    void conditionFingerprint_multiModeStateIn_preservesSemicolonInTuple() {
        // Multi-mode device: "cool;high" is a single tuple, ";" must NOT be used as a split delimiter
        Map<String, DeviceSmvData> deviceMap = buildMultiModeDeviceMap("hvac");

        // IN with two tuples separated by comma: "cool;high,heat;low"
        RuleDto.Condition c = RuleDto.Condition.builder()
                .deviceName("hvac").targetType("state").attribute("state").relation("in").value("cool;high,heat;low").build();

        String fp = FixStrategyUtils.conditionFingerprint(c, deviceMap);

        assertNotNull(fp, "fingerprint should not be null for valid multi-mode state IN");
        // cleanRuleValueByRelation with modeCount=2 splits by [,|] only → ["cool;high","heat;low"]
        // Each part cleaned via cleanStateName: "cool;high"→"coolhigh", "heat;low"→"heatlow"
        // Joined with "," → "coolhigh,heatlow"
        // Wrong (modeCount=1) would split by [,;|] → ["cool","high","heat","low"]
        // → cleanStateName each → "cool,high,heat,low"
        assertTrue(fp.contains("coolhigh,heatlow"),
                "Multi-mode IN fingerprint must preserve ; within tuples, got: " + fp);
        // Verify it does NOT contain the broken single-mode split pattern
        assertFalse(fp.contains("|cool,high,heat,low"),
                "Must not split ; as delimiter for multi-mode device, got: " + fp);
    }

    @Test
    void conditionFingerprint_multiModeStateNotIn_preservesSemicolonInTuple() {
        Map<String, DeviceSmvData> deviceMap = buildMultiModeDeviceMap("hvac");

        RuleDto.Condition c = RuleDto.Condition.builder()
                .deviceName("hvac").targetType("state").attribute("state").relation("not in").value("off;off").build();

        String fp = FixStrategyUtils.conditionFingerprint(c, deviceMap);

        assertNotNull(fp);
        // Single tuple "off;off" → cleanStateName → "offoff" or "off_off"
        // Wrong split would give "off,off" (two separate entries)
        String[] parts = fp.split("\\|");
        assertEquals(5, parts.length, "fingerprint must have 5 pipe-separated segments: " + fp);
        assertEquals("not in", parts[3], "relation segment");
        // The value segment should be a single cleaned tuple, not comma-separated two "off"s
        String valSegment = parts[4];
        assertFalse("off,off".equals(valSegment),
                "NOT_IN fingerprint must not split ; into two entries for multi-mode, got: " + fp);
    }

    @Test
    void conditionFingerprint_singleModeStateIn_splitsSemicolon() {
        // Single-mode device: ";" IS a delimiter → "on;off" → ["on","off"]
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");

        RuleDto.Condition c = RuleDto.Condition.builder()
                .deviceName("sensor").targetType("state").attribute("state").relation("in").value("on;off").build();

        String fp = FixStrategyUtils.conditionFingerprint(c, deviceMap);

        assertNotNull(fp);
        // modeCount=1 → splitStateRuleValues uses [,;|] → ["on","off"]
        // cleanStateName each → "on","off" → joined "on,off"
        assertTrue(fp.contains("on,off"),
                "Single-mode IN fingerprint must split ; as delimiter, got: " + fp);
    }

    // ======================== LOW: maxCandidatesPerRule boundary ========================

    @Test
    void extractCandidateConditions_zeroBudget_returnsEmpty() {
        Map<String, DeviceSmvData> deviceMap = buildDeviceMap("sensor");
        RuleDto rule = RuleDto.builder().conditions(new ArrayList<>()).build();
        SpecificationDto spec = buildSpec(
                buildSpecCond("sensor", "variable", "temperature", ">", "30"));

        List<RuleDto.Condition> candidates = FixStrategyUtils.extractCandidateConditions(
                spec, rule, deviceMap, 0);

        assertTrue(candidates.isEmpty(), "maxCandidatesPerRule=0 should return empty");
    }
}
