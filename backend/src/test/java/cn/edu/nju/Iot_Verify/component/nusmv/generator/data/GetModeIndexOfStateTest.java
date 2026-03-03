package cn.edu.nju.Iot_Verify.component.nusmv.generator.data;

import org.junit.jupiter.api.DisplayName;
import org.junit.jupiter.api.Nested;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Regression + bug-fix tests for {@link DeviceSmvDataFactory#getModeIndexOfState}.
 */
class GetModeIndexOfStateTest {

    // ── helpers ──

    private static DeviceSmvData singleMode(String modeName, String... states) {
        DeviceSmvData smv = new DeviceSmvData();
        smv.getModes().add(modeName);
        List<String> list = new ArrayList<>(List.of(states));
        smv.getModeStates().put(modeName, list);
        return smv;
    }

    private static DeviceSmvData twoModes(String mode0, List<String> states0,
                                           String mode1, List<String> states1) {
        DeviceSmvData smv = new DeviceSmvData();
        smv.getModes().add(mode0);
        smv.getModes().add(mode1);
        smv.getModeStates().put(mode0, new ArrayList<>(states0));
        smv.getModeStates().put(mode1, new ArrayList<>(states1));
        return smv;
    }

    // ── null / empty guards ──

    @Nested
    @DisplayName("Null & empty guards")
    class NullGuards {
        @Test void nullSmv_returnsNeg1() {
            assertEquals(-1, DeviceSmvDataFactory.getModeIndexOfState(null, "cool"));
        }
        @Test void nullState_returnsNeg1() {
            assertEquals(-1, DeviceSmvDataFactory.getModeIndexOfState(singleMode("Mode", "on"), null));
        }
        @Test void emptyModes_returnsNeg1() {
            DeviceSmvData smv = new DeviceSmvData(); // modes is empty list
            assertEquals(-1, DeviceSmvDataFactory.getModeIndexOfState(smv, "cool"));
        }
    }

    // ── semicolon-split strategy (multi-mode devices) ──

    @Nested
    @DisplayName("Semicolon-split multi-mode states")
    class SemicolonSplit {
        @Test void leadingSemicolon_returnsSecondMode() {
            DeviceSmvData smv = twoModes(
                    "LockState", List.of("locked", "unlocked"),
                    "DoorState", List.of("open", "closed"));
            assertEquals(1, DeviceSmvDataFactory.getModeIndexOfState(smv, ";open"));
        }

        @Test void trailingSemicolon_returnsFirstMode() {
            DeviceSmvData smv = twoModes(
                    "LockState", List.of("locked", "unlocked"),
                    "DoorState", List.of("open", "closed"));
            assertEquals(0, DeviceSmvDataFactory.getModeIndexOfState(smv, "locked;"));
        }

        @Test void bothSegments_returnsFirstNonEmpty() {
            DeviceSmvData smv = twoModes(
                    "ModeA", List.of("a1", "a2"),
                    "ModeB", List.of("b1", "b2"));
            assertEquals(0, DeviceSmvDataFactory.getModeIndexOfState(smv, "a1;b1"));
        }
    }

    // ── state-list lookup strategy (single-mode) ──

    @Nested
    @DisplayName("State list membership lookup")
    class StateListLookup {
        @Test void exactStateMatch_singleMode() {
            DeviceSmvData smv = singleMode("ThermostatMode", "cool", "heat", "off");
            assertEquals(0, DeviceSmvDataFactory.getModeIndexOfState(smv, "cool"));
        }

        @Test void stateInSecondMode_twoModes() {
            DeviceSmvData smv = twoModes(
                    "ThermostatFanMode", List.of("auto", "manual"),
                    "ThermostatMode", List.of("cool", "heat"));
            // "cool" is in ThermostatMode (index 1)
            assertEquals(1, DeviceSmvDataFactory.getModeIndexOfState(smv, "cool"));
        }
    }

    // ── mode-name matching strategy ──

    @Nested
    @DisplayName("Mode name matching")
    class ModeNameMatch {
        @Test void stateEqualsModeName() {
            DeviceSmvData smv = twoModes(
                    "ModeA", List.of("a1"),
                    "ModeB", List.of("b1"));
            // state exactly equals a mode name -> that mode's index
            assertEquals(0, DeviceSmvDataFactory.getModeIndexOfState(smv, "ModeA"));
        }

        @Test void stateStartsWithModeName_underscore() {
            DeviceSmvData smv = twoModes(
                    "ModeA", List.of("a1"),
                    "ModeB", List.of("b1"));
            // "ModeA_cool" starts with "ModeA_"
            assertEquals(0, DeviceSmvDataFactory.getModeIndexOfState(smv, "ModeA_cool"));
        }
    }

    // ── SUBSTRING BUG regression tests ──

    @Nested
    @DisplayName("Substring bug: must NOT match mode as arbitrary substring")
    class SubstringBugRegression {

        @Test
        @DisplayName("mode 'on' must NOT match state 'offline'")
        void modeOn_stateOffline_noMatch() {
            DeviceSmvData smv = singleMode("on", "on", "off");
            // "offline" is NOT in the state list and NOT "on" with _ boundary
            // It should return -1 (or match via state list if "offline" were in the list)
            int result = DeviceSmvDataFactory.getModeIndexOfState(smv, "offline");
            assertEquals(-1, result, "mode 'on' should NOT match state 'offline' via substring");
        }

        @Test
        @DisplayName("mode 'Mode' must NOT match state 'ThermostatMode_cool'")
        void shortMode_longCompound_noSubstringMatch() {
            DeviceSmvData smv = twoModes(
                    "Mode", List.of("x"),
                    "ThermostatMode", List.of("cool"));
            // "ThermostatMode_cool" should match "ThermostatMode" (index 1),
            // NOT "Mode" (index 0) via substring
            int result = DeviceSmvDataFactory.getModeIndexOfState(smv, "ThermostatMode_cool");
            assertEquals(1, result,
                    "Should match 'ThermostatMode' (idx 1), not 'Mode' (idx 0) via substring");
        }

        @Test
        @DisplayName("mode 'heat' must NOT match state 'heatingMode'")
        void modeHeat_stateHeatingMode_noMatch() {
            DeviceSmvData smv = singleMode("heat", "heat", "cool");
            int result = DeviceSmvDataFactory.getModeIndexOfState(smv, "heatingMode");
            assertEquals(-1, result,
                    "mode 'heat' should NOT match 'heatingMode' via substring");
        }
    }

    // ── not found ──

    @Nested
    @DisplayName("State not found")
    class NotFound {
        @Test void unknownState_returnsNeg1() {
            DeviceSmvData smv = singleMode("Mode", "on", "off");
            assertEquals(-1, DeviceSmvDataFactory.getModeIndexOfState(smv, "unknown"));
        }
    }
}
