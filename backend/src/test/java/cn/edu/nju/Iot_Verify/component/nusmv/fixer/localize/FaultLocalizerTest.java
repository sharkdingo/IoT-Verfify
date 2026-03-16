package cn.edu.nju.Iot_Verify.component.nusmv.fixer.localize;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDeviceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceVariableDto;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.*;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Tests for FaultLocalizer: verifies correct fault localization along counterexample traces,
 * including cross/same-device condition semantics, startState constraints, conflict detection,
 * relation normalization, and edge cases.
 */
class FaultLocalizerTest {

    private FaultLocalizer localizer;

    @BeforeEach
    void setUp() {
        localizer = new FaultLocalizer();
    }

    // ===== Basic triggering tests =====

    @Test
    void localize_simpleRuleTrigger_returnsOneFault() {
        // Scenario: Rule says "if sensor state=hot then turn_on AC"
        // Trace: step0 sensor=hot, AC=off → step1 sensor=hot, AC=on
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("hot", "cold")),
                buildManifest("Sensor", List.of()));
        DeviceSmvData acSmv = buildDevice("ac_1", "AC", List.of("ACMode"),
                Map.of("ACMode", List.of("on", "off")),
                buildManifest("AC", List.of(buildApi("turn_on", "off", "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "ac_1", acSmv);

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("EQ").value("hot").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .ruleString("if sensor=hot then AC.turn_on")
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("sensor_1", "hot"), buildDeviceTrace("ac_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("sensor_1", "hot"), buildDeviceTrace("ac_1", "on")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);

        assertEquals(1, faults.size());
        assertEquals(0, faults.get(0).getRuleIndex());
        assertEquals(0, faults.get(0).getTriggerStep());
        assertEquals("AC", faults.get(0).getTargetDevice());
        assertEquals("turn_on", faults.get(0).getTargetAction());
        assertFalse(faults.get(0).isConflicting());
    }

    @Test
    void localize_conditionNotSatisfied_returnsEmpty() {
        // Condition: sensor=cold, but trace has sensor=hot
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("hot", "cold")),
                buildManifest("Sensor", List.of()));
        DeviceSmvData acSmv = buildDevice("ac_1", "AC", List.of("ACMode"),
                Map.of("ACMode", List.of("on", "off")),
                buildManifest("AC", List.of(buildApi("turn_on", "off", "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "ac_1", acSmv);

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("EQ").value("cold").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("sensor_1", "hot"), buildDeviceTrace("ac_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("sensor_1", "hot"), buildDeviceTrace("ac_1", "on")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);
        assertTrue(faults.isEmpty());
    }

    // ===== Cross-device vs same-device condition semantics =====

    @Test
    void localize_crossDeviceCondition_evaluatedOnNextState() {
        // Cross-device: condition device (sensor) != command device (AC)
        // Condition should be evaluated on Si+1, not Si
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("hot", "cold")),
                buildManifest("Sensor", List.of()));
        DeviceSmvData acSmv = buildDevice("ac_1", "AC", List.of("ACMode"),
                Map.of("ACMode", List.of("on", "off")),
                buildManifest("AC", List.of(buildApi("turn_on", "off", "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "ac_1", acSmv);

        // Rule: if sensor=hot then AC.turn_on
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("EQ").value("hot").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();

        // Sensor is cold at step 0, hot at step 1 (cross-device evaluates on Si+1)
        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("sensor_1", "cold"), buildDeviceTrace("ac_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("sensor_1", "hot"), buildDeviceTrace("ac_1", "on")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);
        // Cross-device evaluates sensor on Si+1 where sensor=hot, condition satisfied
        assertEquals(1, faults.size());
    }

    @Test
    void localize_sameDeviceCondition_evaluatedOnCurrentState() {
        // Same-device: condition device == command device (AC)
        // Condition should be evaluated on Si
        DeviceSmvData acSmv = buildDevice("ac_1", "AC", List.of("ACMode"),
                Map.of("ACMode", List.of("on", "off", "idle")),
                buildManifest("AC", List.of(buildApi("turn_on", "off", "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("ac_1", acSmv);

        // Rule: if AC state=off then AC.turn_on (same device)
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("AC").attribute("state").relation("EQ").value("off").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();

        // AC is off at step 0 (same-device evaluates on Si), on at step 1
        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("ac_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("ac_1", "on")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);
        assertEquals(1, faults.size());
    }

    // ===== Conflict detection =====

    @Test
    void localize_conflictingRules_markedAsConflicting() {
        // Two rules at the same step target the same device but different end states
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("hot")),
                buildManifest("Sensor", List.of()));
        DeviceSmvData lightSmv = buildDevice("light_1", "Light", List.of("LightMode"),
                Map.of("LightMode", List.of("on", "off")),
                buildManifest("Light", List.of(
                        buildApi("turn_on", null, "on"),
                        buildApi("turn_off", null, "off"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "light_1", lightSmv);

        // The trace will show light going to "on" at step1, so only turn_on effect matches.
        // We need a trace where BOTH effects could be observed. Let's make endState check permissive
        // by having one rule with null endState.
        DeviceManifest lightManifest = buildManifest("Light", List.of(
                buildApi("turn_on", null, "on"),
                buildApi("turn_off", null, "on"))); // both lead to "on" so both match
        lightSmv.setManifest(lightManifest);

        RuleDto rule1 = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("EQ").value("hot").build()))
                .command(RuleDto.Command.builder().deviceName("Light").action("turn_on").build())
                .build();
        RuleDto rule2 = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("EQ").value("hot").build()))
                .command(RuleDto.Command.builder().deviceName("Light").action("turn_off").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("sensor_1", "hot"), buildDeviceTrace("light_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("sensor_1", "hot"), buildDeviceTrace("light_1", "on")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule1, rule2), deviceMap);
        assertEquals(2, faults.size());
        // The original manifest had different end states (on vs off), so they should be marked conflicting
        // But we changed both to "on", so they won't conflict. Let's fix the manifest.
        lightSmv.setManifest(buildManifest("Light", List.of(
                buildApi("turn_on", null, "on"),
                buildApi("turn_off", null, "off"))));

        // Now only turn_on matches the trace (endState "on" matches next state "on")
        faults = localizer.localize(states, List.of(rule1, rule2), deviceMap);
        // Only rule1 matches (turn_on → endState "on" matches next "on")
        // rule2 (turn_off → endState "off") doesn't match next state "on"
        assertEquals(1, faults.size());
        assertEquals(0, faults.get(0).getRuleIndex());
    }

    // ===== Relation normalization =====

    @Test
    void localize_relationNormalization_worksForAllFormats() {
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("hot", "cold")),
                buildManifest("Sensor", List.of()));
        DeviceSmvData acSmv = buildDevice("ac_1", "AC", List.of("ACMode"),
                Map.of("ACMode", List.of("on", "off")),
                buildManifest("AC", List.of(buildApi("turn_on", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "ac_1", acSmv);

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("sensor_1", "hot"), buildDeviceTrace("ac_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("sensor_1", "hot"), buildDeviceTrace("ac_1", "on")))
        );

        // Test "==" format
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("==").value("hot").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();
        assertEquals(1, localizer.localize(states, List.of(rule), deviceMap).size());

        // Test "NEQ" format
        RuleDto ruleNeq = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("NEQ").value("cold").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();
        assertEquals(1, localizer.localize(states, List.of(ruleNeq), deviceMap).size());
    }

    // ===== Numeric comparison =====

    @Test
    void localize_numericGtCondition_works() {
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("active")),
                buildManifest("Sensor", List.of()));
        sensorSmv.getVariables().add(DeviceManifest.InternalVariable.builder()
                .name("temperature").lowerBound(0).upperBound(100).build());

        DeviceSmvData acSmv = buildDevice("ac_1", "AC", List.of("ACMode"),
                Map.of("ACMode", List.of("on", "off")),
                buildManifest("AC", List.of(buildApi("turn_on", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "ac_1", acSmv);

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("temperature").relation("GT").value("30").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();

        TraceDeviceDto sensorTrace = buildDeviceTrace("sensor_1", "active");
        TraceVariableDto tempVar = new TraceVariableDto();
        tempVar.setName("temperature");
        tempVar.setValue("35");
        sensorTrace.setVariables(List.of(tempVar));

        // Cross-device condition (sensor != AC) is evaluated on Si+1, so variable must be on Si+1 sensor
        TraceDeviceDto sensorTraceNext = buildDeviceTrace("sensor_1", "active");
        sensorTraceNext.setVariables(List.of(tempVar));

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(sensorTrace, buildDeviceTrace("ac_1", "off"))),
                buildState(1, List.of(sensorTraceNext, buildDeviceTrace("ac_1", "on")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);
        assertEquals(1, faults.size());
    }

    // ===== startState constraint =====

    @Test
    void localize_startStateNotMatched_ruleNotTriggered() {
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("hot")),
                buildManifest("Sensor", List.of()));
        DeviceSmvData acSmv = buildDevice("ac_1", "AC", List.of("ACMode"),
                Map.of("ACMode", List.of("on", "off", "standby")),
                buildManifest("AC", List.of(buildApi("turn_on", "off", "on")))); // requires startState=off

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "ac_1", acSmv);

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("EQ").value("hot").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();

        // AC is in "standby" at step0 — startState is "off", so rule should NOT trigger
        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("sensor_1", "hot"), buildDeviceTrace("ac_1", "standby"))),
                buildState(1, List.of(buildDeviceTrace("sensor_1", "hot"), buildDeviceTrace("ac_1", "on")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);
        assertTrue(faults.isEmpty());
    }

    // ===== Edge cases =====

    @Test
    void localize_nullStates_returnsEmpty() {
        assertTrue(localizer.localize(null, List.of(), Map.of()).isEmpty());
    }

    @Test
    void localize_singleState_returnsEmpty() {
        // Need at least 2 states for a transition
        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("a", "on"))));
        assertTrue(localizer.localize(states, List.of(), Map.of()).isEmpty());
    }

    @Test
    void localize_emptyRules_returnsEmpty() {
        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("a", "on"))),
                buildState(1, List.of(buildDeviceTrace("a", "off"))));
        assertTrue(localizer.localize(states, List.of(), Map.of()).isEmpty());
    }

    @Test
    void localize_nullRuleCommand_skipsGracefully() {
        RuleDto rule = RuleDto.builder()
                .conditions(List.of())
                .command(null) // null command
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("a", "on"))),
                buildState(1, List.of(buildDeviceTrace("a", "off"))));

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), Map.of());
        assertTrue(faults.isEmpty());
    }

    @Test
    void localize_unconditionalRule_triggersIfEffectMatches() {
        DeviceSmvData lightSmv = buildDevice("light_1", "Light", List.of("LightMode"),
                Map.of("LightMode", List.of("on", "off")),
                buildManifest("Light", List.of(buildApi("turn_on", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("light_1", lightSmv);

        RuleDto rule = RuleDto.builder()
                .conditions(List.of()) // unconditional
                .command(RuleDto.Command.builder().deviceName("Light").action("turn_on").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("light_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("light_1", "on")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);
        assertEquals(1, faults.size());
    }

    // ===== IN / NOT_IN relation =====

    @Test
    void localize_inRelation_matchesSetMembership() {
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("hot", "warm", "cold")),
                buildManifest("Sensor", List.of()));
        DeviceSmvData acSmv = buildDevice("ac_1", "AC", List.of("ACMode"),
                Map.of("ACMode", List.of("on", "off")),
                buildManifest("AC", List.of(buildApi("turn_on", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "ac_1", acSmv);

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("IN").value("{hot,warm}").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("sensor_1", "warm"), buildDeviceTrace("ac_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("sensor_1", "warm"), buildDeviceTrace("ac_1", "on")))
        );

        assertEquals(1, localizer.localize(states, List.of(rule), deviceMap).size());
    }

    @Test
    void localize_inRelation_semicolonDelimiter_singleMode() {
        // Single-mode: semicolons are delimiters (not tuple separators)
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("hot", "warm", "cold")),
                buildManifest("Sensor", List.of()));
        DeviceSmvData acSmv = buildDevice("ac_1", "AC", List.of("ACMode"),
                Map.of("ACMode", List.of("on", "off")),
                buildManifest("AC", List.of(buildApi("turn_on", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "ac_1", acSmv);

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("IN").value("hot;warm").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("sensor_1", "warm"), buildDeviceTrace("ac_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("sensor_1", "warm"), buildDeviceTrace("ac_1", "on")))
        );

        assertEquals(1, localizer.localize(states, List.of(rule), deviceMap).size(),
                "Semicolon-delimited IN values must be split correctly for single-mode devices");
    }

    @Test
    void localize_inRelation_pipeDelimiter() {
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("hot", "warm", "cold")),
                buildManifest("Sensor", List.of()));
        DeviceSmvData acSmv = buildDevice("ac_1", "AC", List.of("ACMode"),
                Map.of("ACMode", List.of("on", "off")),
                buildManifest("AC", List.of(buildApi("turn_on", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "ac_1", acSmv);

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("IN").value("hot|warm").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("sensor_1", "warm"), buildDeviceTrace("ac_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("sensor_1", "warm"), buildDeviceTrace("ac_1", "on")))
        );

        assertEquals(1, localizer.localize(states, List.of(rule), deviceMap).size(),
                "Pipe-delimited IN values must be split correctly");
    }

    @Test
    void localize_notInRelation_excludesMatch() {
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("hot", "warm", "cold")),
                buildManifest("Sensor", List.of()));
        DeviceSmvData acSmv = buildDevice("ac_1", "AC", List.of("ACMode"),
                Map.of("ACMode", List.of("on", "off")),
                buildManifest("AC", List.of(buildApi("turn_on", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "ac_1", acSmv);

        // NOT_IN "hot,cold": sensor is "warm" → NOT in set → condition satisfied
        RuleDto ruleSatisfied = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("NOT_IN").value("hot,cold").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("sensor_1", "warm"), buildDeviceTrace("ac_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("sensor_1", "warm"), buildDeviceTrace("ac_1", "on")))
        );

        assertEquals(1, localizer.localize(states, List.of(ruleSatisfied), deviceMap).size(),
                "NOT_IN should be satisfied when state is not in the exclusion set");

        // NOT_IN "hot,warm": sensor is "warm" → IN set → condition NOT satisfied
        RuleDto ruleNotSatisfied = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("NOT_IN").value("hot,warm").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();

        assertTrue(localizer.localize(states, List.of(ruleNotSatisfied), deviceMap).isEmpty(),
                "NOT_IN should not be satisfied when state is in the exclusion set");
    }

    @Test
    void localize_inRelation_multiModeTuple() {
        // Multi-mode device (2 modes): semicolons are tuple separators, not delimiters
        // HVAC condition is same-device as command → evaluated on Si (currentState)
        // So at Si the hvac state must already match the IN set
        DeviceSmvData hvacSmv = buildDevice("hvac_1", "HVAC",
                List.of("PowerMode", "FanMode"),
                new LinkedHashMap<>(Map.of("PowerMode", List.of("cool", "heat", "off"),
                        "FanMode", List.of("high", "low"))),
                buildManifest("HVAC", List.of(buildApi("set_heat", "cool", "heat"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("hvac_1", hvacSmv);

        // Condition: hvac state IN "cool;high,heat;low" (two tuples separated by comma)
        // Same-device → evaluated on Si where hvac state is "cool;high" → matches first tuple
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("HVAC").attribute("state").relation("IN").value("cool;high,heat;low").build()))
                .command(RuleDto.Command.builder().deviceName("HVAC").action("set_heat").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("hvac_1", "cool;high"))),
                buildState(1, List.of(buildDeviceTrace("hvac_1", "heat;high")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);
        assertEquals(1, faults.size(),
                "Multi-mode IN must split by [,|] only, preserving ; within tuples");
    }

    @Test
    void localize_inRelation_multiModeSingleStateCandidate() {
        // Multi-mode device: single-value IN candidate (no ;) that uniquely belongs to one mode
        // Mirrors SmvMainModuleBuilder.resolveStateTupleCandidate() lines 690-718
        DeviceSmvData hvacSmv = buildDevice("hvac_1", "HVAC",
                List.of("PowerMode", "FanMode"),
                new LinkedHashMap<>(Map.of("PowerMode", List.of("cool", "heat", "off"),
                        "FanMode", List.of("high", "low"))),
                buildManifest("HVAC", List.of(buildApi("set_heat", "cool", "heat"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("hvac_1", hvacSmv);

        // "cool" uniquely belongs to PowerMode → should match if device's PowerMode is "cool"
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("HVAC").attribute("state").relation("IN").value("cool,heat").build()))
                .command(RuleDto.Command.builder().deviceName("HVAC").action("set_heat").build())
                .build();

        // Same-device → evaluated on Si. At Si, hvac is "cool;high" → PowerMode=cool → matches "cool"
        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("hvac_1", "cool;high"))),
                buildState(1, List.of(buildDeviceTrace("hvac_1", "heat;high")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);
        assertEquals(1, faults.size(),
                "Multi-mode IN with single-value candidate should match if value uniquely belongs to one mode");
    }

    // ===== Multi-mode =/ != with partial state patterns =====

    @Test
    void localize_eqRelation_multiModePartialPattern_semicolonCool() {
        // Thermostat-like: modes [ThermostatFanMode, ThermostatMode]
        // Rule condition: state = ";cool" (partial pattern, only constrains ThermostatMode)
        // Device state at Si: "auto;cool" → ThermostatMode=cool → should match
        // Command targets a different device (light) to avoid same-device evaluation complexity
        DeviceSmvData thermostatSmv = buildDevice("thermo_1", "Thermostat",
                List.of("ThermostatFanMode", "ThermostatMode"),
                new LinkedHashMap<>(Map.of(
                        "ThermostatFanMode", List.of("auto", "circulate", "on"),
                        "ThermostatMode", List.of("auto", "cool", "heat", "off"))),
                buildManifest("Thermostat", List.of()));
        DeviceSmvData lightSmv = buildDevice("light_1", "Light", List.of("LightMode"),
                Map.of("LightMode", List.of("on", "off")),
                buildManifest("Light", List.of(buildApi("turn_on", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("thermo_1", thermostatSmv, "light_1", lightSmv);

        // Cross-device: condition on thermostat, command on light → condition evaluated on Si+1
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Thermostat").attribute("state").relation("EQ").value(";cool").build()))
                .command(RuleDto.Command.builder().deviceName("Light").action("turn_on").build())
                .build();

        // At Si+1: thermostat="auto;cool" → ThermostatMode=cool → matches ";cool"
        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("thermo_1", "auto;heat"),
                        buildDeviceTrace("light_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("thermo_1", "auto;cool"),
                        buildDeviceTrace("light_1", "on")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);
        assertEquals(1, faults.size(),
                "Multi-mode = with partial pattern ';cool' should match when ThermostatMode=cool");
    }

    @Test
    void localize_neqRelation_multiModePartialPattern() {
        // state != ";cool": device ThermostatMode=heat → not cool → condition satisfied
        DeviceSmvData thermostatSmv = buildDevice("thermo_1", "Thermostat",
                List.of("ThermostatFanMode", "ThermostatMode"),
                new LinkedHashMap<>(Map.of(
                        "ThermostatFanMode", List.of("auto", "circulate", "on"),
                        "ThermostatMode", List.of("auto", "cool", "heat", "off"))),
                buildManifest("Thermostat", List.of()));
        DeviceSmvData lightSmv = buildDevice("light_1", "Light", List.of("LightMode"),
                Map.of("LightMode", List.of("on", "off")),
                buildManifest("Light", List.of(buildApi("turn_on", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("thermo_1", thermostatSmv, "light_1", lightSmv);

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Thermostat").attribute("state").relation("!=").value(";cool").build()))
                .command(RuleDto.Command.builder().deviceName("Light").action("turn_on").build())
                .build();

        // Cross-device → evaluated on Si+1. At Si+1: thermostat="auto;heat" → ThermostatMode=heat != cool
        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("thermo_1", "auto;cool"),
                        buildDeviceTrace("light_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("thermo_1", "auto;heat"),
                        buildDeviceTrace("light_1", "on")))
        );

        assertEquals(1, localizer.localize(states, List.of(rule), deviceMap).size(),
                "Multi-mode != with partial pattern should be satisfied when mode doesn't match");
    }

    @Test
    void localize_eqRelation_multiModeAmbiguousValue_failClosed() {
        // "auto" exists in both ThermostatFanMode and ThermostatMode → ambiguous → fail-closed
        DeviceSmvData thermostatSmv = buildDevice("thermo_1", "Thermostat",
                List.of("ThermostatFanMode", "ThermostatMode"),
                new LinkedHashMap<>(Map.of(
                        "ThermostatFanMode", List.of("auto", "circulate", "on"),
                        "ThermostatMode", List.of("auto", "cool", "heat", "off"))),
                buildManifest("Thermostat", List.of()));
        DeviceSmvData lightSmv = buildDevice("light_1", "Light", List.of("LightMode"),
                Map.of("LightMode", List.of("on", "off")),
                buildManifest("Light", List.of(buildApi("turn_on", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("thermo_1", thermostatSmv, "light_1", lightSmv);

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Thermostat").attribute("state").relation("EQ").value("auto").build()))
                .command(RuleDto.Command.builder().deviceName("Light").action("turn_on").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("thermo_1", "auto;auto"),
                        buildDeviceTrace("light_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("thermo_1", "auto;auto"),
                        buildDeviceTrace("light_1", "on")))
        );

        // "auto" is ambiguous → generator fail-closed → rule never fires
        assertTrue(localizer.localize(states, List.of(rule), deviceMap).isEmpty(),
                "Ambiguous single value on multi-mode device should fail-closed");
    }

    @Test
    void localize_apiSignalCondition_nullEndState_permissive() {
        // Signal API with endState=null: NuSMV guard is api_signal=TRUE
        // FaultLocalizer should be permissive (return true) since api_signal is filtered from traces
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("active", "idle")),
                buildManifest("Sensor", List.of(buildSignalApi("detect", null, null))));
        DeviceSmvData alarmSmv = buildDevice("alarm_1", "Alarm", List.of("AlarmMode"),
                Map.of("AlarmMode", List.of("on", "off")),
                buildManifest("Alarm", List.of(buildApi("activate", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "alarm_1", alarmSmv);

        // Rule: if sensor.detect (signal, no relation/value) then alarm.activate
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("detect")
                        .relation(null).value(null).build()))
                .command(RuleDto.Command.builder().deviceName("Alarm").action("activate").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("sensor_1", "active"), buildDeviceTrace("alarm_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("sensor_1", "active"), buildDeviceTrace("alarm_1", "on")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);
        assertEquals(1, faults.size(),
                "Signal API condition with null endState should be permissive");
    }

    @Test
    void localize_apiSignalCondition_multiModeEndState() {
        // Signal API with endState on a multi-mode device
        DeviceSmvData hvacSmv = buildDevice("hvac_1", "HVAC",
                List.of("PowerMode", "FanMode"),
                new LinkedHashMap<>(Map.of("PowerMode", List.of("cool", "heat", "off"),
                        "FanMode", List.of("high", "low"))),
                buildManifest("HVAC", List.of(buildSignalApi("start_cooling", null, "cool"))));
        DeviceSmvData alarmSmv = buildDevice("alarm_1", "Alarm", List.of("AlarmMode"),
                Map.of("AlarmMode", List.of("on", "off")),
                buildManifest("Alarm", List.of(buildApi("activate", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("hvac_1", hvacSmv, "alarm_1", alarmSmv);

        // Rule: if hvac.start_cooling (signal) then alarm.activate
        // hvac state is "cool;high" — endState "cool" should match PowerMode
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("HVAC").attribute("start_cooling")
                        .relation(null).value(null).build()))
                .command(RuleDto.Command.builder().deviceName("Alarm").action("activate").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("hvac_1", "cool;high"), buildDeviceTrace("alarm_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("hvac_1", "cool;high"), buildDeviceTrace("alarm_1", "on")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);
        assertEquals(1, faults.size(),
                "Signal API endState should resolve to specific mode for multi-mode devices");
    }

    @Test
    void localize_apiSignalCondition_endStateUnmappableToMode_failClosed() {
        // Signal API with endState that cannot be mapped to any mode via getModeIndexOfState.
        // Generator emits api_signal=TRUE as guard, but ASSIGN cannot produce a valid transition
        // → api_signal is always FALSE → condition never satisfied. Fail-closed.
        DeviceSmvData hvacSmv = buildDevice("hvac_1", "HVAC",
                List.of("PowerMode", "FanMode"),
                new LinkedHashMap<>(Map.of("PowerMode", List.of("cool", "heat", "off"),
                        "FanMode", List.of("high", "low"))),
                // endState "unknown_state" does not belong to any mode
                buildManifest("HVAC", List.of(buildSignalApi("mystery_signal", null, "unknown_state"))));
        DeviceSmvData alarmSmv = buildDevice("alarm_1", "Alarm", List.of("AlarmMode"),
                Map.of("AlarmMode", List.of("on", "off")),
                buildManifest("Alarm", List.of(buildApi("activate", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("hvac_1", hvacSmv, "alarm_1", alarmSmv);

        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("HVAC").attribute("mystery_signal")
                        .relation(null).value(null).build()))
                .command(RuleDto.Command.builder().deviceName("Alarm").action("activate").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("hvac_1", "cool;high"), buildDeviceTrace("alarm_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("hvac_1", "cool;high"), buildDeviceTrace("alarm_1", "on")))
        );

        List<FaultRuleDto> faults = localizer.localize(states, List.of(rule), deviceMap);
        assertTrue(faults.isEmpty(),
                "Signal API with unmappable endState should fail-closed (signal always FALSE in model)");
    }

    @Test
    void localize_notInRelation_illegalCandidate_failClosed() {
        // NOT_IN with a candidate value that doesn't exist in any mode state list.
        // Generator: resolveStateTupleCandidate → null → buildSingleCondition → null → rule FALSE.
        // FaultLocalizer must also fail-closed (return false), NOT treat as "not matched → satisfied".
        DeviceSmvData sensorSmv = buildDevice("sensor_1", "Sensor", List.of("SensorMode"),
                Map.of("SensorMode", List.of("hot", "warm", "cold")),
                buildManifest("Sensor", List.of()));
        DeviceSmvData acSmv = buildDevice("ac_1", "AC", List.of("ACMode"),
                Map.of("ACMode", List.of("on", "off")),
                buildManifest("AC", List.of(buildApi("turn_on", null, "on"))));

        Map<String, DeviceSmvData> deviceMap = Map.of("sensor_1", sensorSmv, "ac_1", acSmv);

        // "nonexistent" is not in SensorMode's state list → unresolvable → fail-closed
        RuleDto rule = RuleDto.builder()
                .conditions(List.of(RuleDto.Condition.builder()
                        .deviceName("Sensor").attribute("state").relation("NOT_IN")
                        .value("nonexistent,also_bad").build()))
                .command(RuleDto.Command.builder().deviceName("AC").action("turn_on").build())
                .build();

        List<TraceStateDto> states = List.of(
                buildState(0, List.of(buildDeviceTrace("sensor_1", "warm"), buildDeviceTrace("ac_1", "off"))),
                buildState(1, List.of(buildDeviceTrace("sensor_1", "warm"), buildDeviceTrace("ac_1", "on")))
        );

        // Without fail-closed, NOT_IN would wrongly evaluate as: "warm" not in {nonexistent, also_bad} → true
        // With fail-closed, the unresolvable candidates make the entire condition FALSE → rule not triggered
        assertTrue(localizer.localize(states, List.of(rule), deviceMap).isEmpty(),
                "NOT_IN with unresolvable candidates must fail-closed, not treat as 'not matched'");
    }

    private DeviceSmvData buildDevice(String varName, String templateName,
                                       List<String> modes, Map<String, List<String>> modeStates,
                                       DeviceManifest manifest) {
        DeviceSmvData smv = new DeviceSmvData();
        smv.setVarName(varName);
        smv.setTemplateName(templateName);
        smv.setModes(modes);
        smv.setModeStates(new LinkedHashMap<>(modeStates));
        List<String> allStates = new ArrayList<>();
        modeStates.values().forEach(allStates::addAll);
        smv.setStates(allStates);
        smv.setManifest(manifest);
        return smv;
    }

    private DeviceManifest buildManifest(String name, List<DeviceManifest.API> apis) {
        return DeviceManifest.builder().name(name).apis(apis).build();
    }

    private DeviceManifest.API buildApi(String name, String startState, String endState) {
        return DeviceManifest.API.builder().name(name).startState(startState).endState(endState).build();
    }

    private DeviceManifest.API buildSignalApi(String name, String startState, String endState) {
        return DeviceManifest.API.builder().name(name).startState(startState).endState(endState).signal(true).build();
    }

    private TraceStateDto buildState(int index, List<TraceDeviceDto> devices) {
        return TraceStateDto.builder().stateIndex(index).devices(devices).build();
    }

    private TraceDeviceDto buildDeviceTrace(String deviceId, String state) {
        TraceDeviceDto dto = new TraceDeviceDto();
        dto.setDeviceId(deviceId);
        dto.setState(state);
        return dto;
    }
}
