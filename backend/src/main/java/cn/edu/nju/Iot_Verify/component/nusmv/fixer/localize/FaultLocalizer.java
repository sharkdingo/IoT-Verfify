package cn.edu.nju.Iot_Verify.component.nusmv.fixer.localize;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.SmvRelationUtils;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.fix.FaultRuleDto;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDeviceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceVariableDto;
import lombok.extern.slf4j.Slf4j;
import org.springframework.stereotype.Component;

import java.util.*;

/**
 * Fault localizer: identifies which rules were triggered and potentially conflicting
 * along a counterexample trace.
 *
 * Mirrors the NuSMV transition semantics from SmvMainModuleBuilder:
 * - Cross-device conditions (condition.deviceName != command.deviceName) are evaluated on Si+1 (next-state)
 * - Same-device conditions are evaluated on Si (current-state)
 * - startState constraints from the API definition are checked on Si
 * - API signal conditions (relation=null) are inferred from state transitions
 */
@Slf4j
@Component
public class FaultLocalizer {

    /**
     * Localize fault rules from a counterexample trace.
     *
     * @param states        counterexample trace states
     * @param rules         all rules from the verification request
     * @param deviceSmvMap  device SMV data map (from SmvGenerator.buildDeviceSmvMap)
     * @return list of fault rules with trigger step, conflict info, and reasons
     */
    public List<FaultRuleDto> localize(List<TraceStateDto> states,
                                       List<RuleDto> rules,
                                       Map<String, DeviceSmvData> deviceSmvMap) {
        if (states == null || states.size() < 2 || rules == null || rules.isEmpty()) {
            return List.of();
        }

        // For each step transition Si → Si+1, check which rules fire.
        // A "triggered" rule: (1) conditions satisfied, (2) command API matches the state transition.
        List<FaultRuleDto> faultRules = new ArrayList<>();
        Set<String> seenRuleSteps = new HashSet<>(); // avoid duplicates: "ruleIdx:step"

        for (int step = 0; step < states.size() - 1; step++) {
            TraceStateDto currentState = states.get(step);
            TraceStateDto nextState = states.get(step + 1);

            // Collect rules triggered at this step
            List<FaultRuleDto> stepTriggered = new ArrayList<>();

            for (int ruleIdx = 0; ruleIdx < rules.size(); ruleIdx++) {
                RuleDto rule = rules.get(ruleIdx);
                if (rule == null || rule.getCommand() == null || rule.getCommand().getAction() == null) {
                    continue;
                }

                String targetDeviceName = rule.getCommand().getDeviceName();
                String action = rule.getCommand().getAction();
                DeviceSmvData targetSmv = findDevice(targetDeviceName, deviceSmvMap);
                if (targetSmv == null) continue;

                DeviceManifest.API matchedApi = DeviceSmvDataFactory.findApi(targetSmv.getManifest(), action);
                if (matchedApi == null) continue;

                // Check startState constraint
                if (!checkStartState(matchedApi, targetSmv, currentState)) {
                    continue;
                }

                // Check command effect: the target device must transition to the API's endState
                if (!checkCommandEffect(matchedApi, targetSmv, currentState, nextState)) {
                    continue;
                }

                // Evaluate rule conditions using NuSMV semantics
                if (!evaluateConditions(rule, targetSmv, currentState, nextState, deviceSmvMap)) {
                    continue;
                }

                String dedupKey = ruleIdx + ":" + step;
                if (!seenRuleSteps.add(dedupKey)) continue;

                FaultRuleDto fault = FaultRuleDto.builder()
                        .ruleIndex(ruleIdx)
                        .ruleId(rule.getId())
                        .ruleString(rule.getRuleString())
                        .triggerStep(step)
                        .targetDevice(targetDeviceName)
                        .targetAction(action)
                        .build();
                stepTriggered.add(fault);
            }

            // Detect conflicts: two rules at the same step targeting the same device but different end states
            detectConflicts(stepTriggered, rules, deviceSmvMap);
            faultRules.addAll(stepTriggered);
        }

        return faultRules;
    }

    // ===== Condition evaluation =====

    private boolean evaluateConditions(RuleDto rule, DeviceSmvData targetSmv,
                                       TraceStateDto currentState, TraceStateDto nextState,
                                       Map<String, DeviceSmvData> deviceSmvMap) {
        if (rule.getConditions() == null || rule.getConditions().isEmpty()) {
            return true; // unconditional rule always fires
        }

        for (RuleDto.Condition cond : rule.getConditions()) {
            if (cond == null) return false;

            String condDeviceName = cond.getDeviceName();
            String targetVarName = targetSmv.getVarName();
            DeviceSmvData condSmv = findDevice(condDeviceName, deviceSmvMap);
            if (condSmv == null) return false;

            // Mirror SmvMainModuleBuilder semantics:
            // Cross-device conditions → evaluate on next state (Si+1)
            // Same-device conditions → evaluate on current state (Si)
            boolean isSameDevice = targetVarName != null && targetVarName.equals(condSmv.getVarName());
            TraceStateDto evalState = isSameDevice ? currentState : nextState;

            if (!evaluateSingleCondition(cond, condSmv, evalState)) {
                return false;
            }
        }
        return true;
    }

    private boolean evaluateSingleCondition(RuleDto.Condition cond, DeviceSmvData condSmv,
                                            TraceStateDto evalState) {
        String attr = cond.getAttribute();
        if (attr == null || attr.isBlank()) return false;

        TraceDeviceDto devTrace = findDeviceInState(evalState, condSmv);
        if (devTrace == null) return false;

        // API signal condition (relation=null, value=null): check if the API's end state is reached
        if (cond.getRelation() == null && cond.getValue() == null) {
            return evaluateApiSignalCondition(cond, condSmv, devTrace);
        }

        String relation = SmvRelationUtils.normalizeRelation(cond.getRelation());
        String expectedValue = cond.getValue();
        if (relation == null || expectedValue == null) return false;
        if (!SmvRelationUtils.isSupportedRelation(relation)) return false;

        // "state" attribute → compare with device state/mode
        if ("state".equals(attr)) {
            return evaluateStateCondition(devTrace, condSmv, relation, expectedValue);
        }

        // Mode attribute → compare with device state for that mode
        if (condSmv.getModes() != null && condSmv.getModes().contains(attr)) {
            String deviceModeState = getDeviceModeState(devTrace, condSmv, attr);
            return compareValues(deviceModeState, relation, expectedValue);
        }

        // Internal variable
        String varValue = getVariableValue(devTrace, attr);
        if (varValue != null) {
            return compareValues(varValue, relation, expectedValue);
        }

        return false;
    }

    private boolean evaluateApiSignalCondition(RuleDto.Condition cond, DeviceSmvData condSmv,
                                               TraceDeviceDto devTrace) {
        // Find the API by name; it must be a signal API (matching SmvMainModuleBuilder:536)
        DeviceManifest.API api = findSignalApi(condSmv.getManifest(), cond.getAttribute());
        if (api == null) return false;

        String endState = api.getEndState();

        if (endState == null) {
            // NuSMV guard is just api_signal=TRUE (no state fallback).
            // api_signal variables are filtered from traces (_a suffix → isInternalControlVariable),
            // so we cannot check directly. Be permissive to avoid false negatives in fault localization.
            return devTrace != null;
        }

        if (devTrace == null) return false;
        String deviceState = devTrace.getState();
        if (deviceState == null) return false;

        // Multi-mode: resolve endState to specific mode and compare per-mode
        // (mirrors SmvMainModuleBuilder:551-567)
        if (condSmv.getModes() != null && !condSmv.getModes().isEmpty()) {
            int modeIdx = DeviceSmvDataFactory.getModeIndexOfState(condSmv, endState);
            if (modeIdx >= 0 && modeIdx < condSmv.getModes().size()) {
                String mode = condSmv.getModes().get(modeIdx);
                String modeState = getDeviceModeState(devTrace, condSmv, mode);
                if (modeState == null) return false;
                String perModeEnd = extractModeState(endState, modeIdx);
                if (perModeEnd == null) return false;
                String cleanEnd = DeviceSmvDataFactory.cleanStateName(perModeEnd);
                String cleanModeState = DeviceSmvDataFactory.cleanStateName(modeState);
                return Objects.equals(cleanEnd, cleanModeState);
            }
            // endState exists but cannot be mapped to any mode.
            // Generator would emit api_signal=TRUE as the guard, but the ASSIGN section
            // cannot produce a valid transition for this signal → api_signal is always FALSE
            // (SmvMainModuleBuilder:960,998). Fail-closed: condition never satisfied.
            return false;
        }

        // No modes: direct comparison (single-state device)
        String cleanEnd = DeviceSmvDataFactory.cleanStateName(endState);
        String cleanDeviceState = DeviceSmvDataFactory.cleanStateName(deviceState);
        return cleanEnd.equals(cleanDeviceState) || endState.equals(deviceState);
    }

    /**
     * Find a signal API by name. Returns null if the API doesn't exist or is not a signal.
     * Matches SmvMainModuleBuilder's filter: Boolean.TRUE.equals(api.getSignal()).
     */
    private DeviceManifest.API findSignalApi(DeviceManifest manifest, String apiName) {
        if (manifest == null || manifest.getApis() == null || apiName == null) return null;
        for (DeviceManifest.API api : manifest.getApis()) {
            if (apiName.equals(api.getName()) && Boolean.TRUE.equals(api.getSignal())) {
                return api;
            }
        }
        return null;
    }

    private boolean evaluateStateCondition(TraceDeviceDto devTrace, DeviceSmvData condSmv,
                                           String relation, String expectedValue) {
        // For multi-mode devices, state may be semicolon-separated
        String deviceState = devTrace.getState();
        if (deviceState == null) return false;

        // For set relations (in/not in), use mode-aware splitting that matches
        // SmvMainModuleBuilder.splitStateRuleCandidates() semantics.
        if ("in".equals(relation) || "not in".equals(relation)) {
            return evaluateStateInNotIn(devTrace, condSmv, relation, expectedValue);
        }

        // Try direct comparison first (works for single-mode or exact full-tuple match)
        if (compareValues(DeviceSmvDataFactory.cleanStateName(deviceState), relation,
                DeviceSmvDataFactory.cleanStateName(expectedValue))) {
            return true;
        }

        // For single-mode devices, try matching against the mode state
        if (condSmv.getModes() != null && condSmv.getModes().size() == 1) {
            String mode = condSmv.getModes().get(0);
            String modeState = getDeviceModeState(devTrace, condSmv, mode);
            if (modeState != null) {
                return compareValues(DeviceSmvDataFactory.cleanStateName(modeState), relation,
                        DeviceSmvDataFactory.cleanStateName(expectedValue));
            }
        }

        // Multi-mode: resolve expectedValue to a specific mode via resolveStateTupleCandidate semantics.
        // Generator only supports = and != for multi-mode state (SmvMainModuleBuilder:585-591);
        // other relations (>, <, >=, <=) are fail-closed to null → rule FALSE.
        if (condSmv.getModes() != null && condSmv.getModes().size() > 1) {
            if (!"=".equals(relation) && !"!=".equals(relation)) {
                return false; // fail-closed: unsupported relation on multi-mode state
            }
            return evaluateStateEqNeqMultiMode(devTrace, condSmv, relation, expectedValue);
        }

        return false;
    }

    /**
     * Evaluate = or != state conditions on multi-mode devices.
     * Mirrors SmvMainModuleBuilder.resolveStateTupleCandidate() + buildStateTupleExpr():
     * resolves the expected value to per-mode state(s), then compares each resolved mode
     * against the device's per-mode trace state.
     */
    private boolean evaluateStateEqNeqMultiMode(TraceDeviceDto devTrace, DeviceSmvData condSmv,
                                                 String relation, String expectedValue) {
        if (condSmv.getModeStates() == null) return false;

        // Resolve expectedValue to a mode-state map (same logic as resolveStateTupleCandidate)
        Map<String, String> resolvedModes = resolveToModeStateMap(condSmv, expectedValue);
        if (resolvedModes == null || resolvedModes.isEmpty()) {
            // Unresolvable → generator would fail-closed the rule to FALSE
            return false;
        }

        // Compare each resolved mode against device's per-mode state
        // (generator builds: mode0=val0 & mode1=val1; for = we check all match, for != we negate)
        boolean allMatch = true;
        for (Map.Entry<String, String> entry : resolvedModes.entrySet()) {
            String mode = entry.getKey();
            String expectedModeState = entry.getValue();
            String deviceModeState = getDeviceModeState(devTrace, condSmv, mode);
            if (deviceModeState == null) {
                allMatch = false;
                break;
            }
            String cleanExpected = DeviceSmvDataFactory.cleanStateName(expectedModeState);
            String cleanDevice = DeviceSmvDataFactory.cleanStateName(deviceModeState);
            if (!Objects.equals(cleanExpected, cleanDevice)) {
                allMatch = false;
                break;
            }
        }

        return "=".equals(relation) ? allMatch : !allMatch;
    }

    /**
     * Resolve a raw state value to a mode→state map, mirroring
     * SmvMainModuleBuilder.resolveStateTupleCandidate().
     * Returns null if unresolvable (ambiguous, invalid, all-wildcard).
     */
    private Map<String, String> resolveToModeStateMap(DeviceSmvData condSmv, String rawValue) {
        List<String> modes = condSmv.getModes();
        Map<String, List<String>> modeStates = condSmv.getModeStates();
        if (modeStates == null || rawValue == null || rawValue.isBlank()) return null;

        // Tuple pattern (contains ;): split by ; → per-mode
        if (rawValue.contains(";")) {
            String[] segments = rawValue.split(";", -1);
            if (segments.length != modes.size()) return null;
            Map<String, String> result = new LinkedHashMap<>();
            boolean anyNonWildcard = false;
            for (int i = 0; i < modes.size(); i++) {
                String seg = segments[i].trim();
                if (seg.isEmpty()) continue; // wildcard
                anyNonWildcard = true;
                String cleanSeg = DeviceSmvDataFactory.cleanStateName(seg);
                String mode = modes.get(i);
                List<String> legalStates = modeStates.get(mode);
                if (legalStates == null || !legalStates.contains(cleanSeg)) return null;
                result.put(mode, cleanSeg);
            }
            return anyNonWildcard ? result : null;
        }

        // Single value: must uniquely belong to one mode
        String cleanValue = DeviceSmvDataFactory.cleanStateName(rawValue);
        if (cleanValue == null || cleanValue.isEmpty()) return null;

        String matchedMode = null;
        for (String mode : modes) {
            List<String> legalStates = modeStates.get(mode);
            if (legalStates != null && legalStates.contains(cleanValue)) {
                if (matchedMode != null) return null; // ambiguous
                matchedMode = mode;
            }
        }
        if (matchedMode == null) return null;
        return Map.of(matchedMode, cleanValue);
    }

    /**
     * Mode-aware IN/NOT_IN evaluation for state conditions.
     * Mirrors SmvMainModuleBuilder.splitStateRuleCandidates() + resolveStateTupleCandidate() semantics.
     */
    private boolean evaluateStateInNotIn(TraceDeviceDto devTrace, DeviceSmvData condSmv,
                                          String relation, String expectedValue) {
        int modeCount = (condSmv.getModes() != null) ? condSmv.getModes().size() : 0;
        if (modeCount == 0) return false; // state conditions require modes

        // Strip braces/brackets defensively (values may arrive as "{hot,warm}" or "[hot,warm]")
        String cleanedValue = expectedValue.replaceAll("[{}\\[\\]()]", "").trim();
        // Mode-aware split: multi-mode preserves ';' within tuples, single-mode splits on [,;|]
        List<String> candidates = SmvRelationUtils.splitStateRuleValues(cleanedValue, modeCount);
        if (candidates.isEmpty()) return false;

        // Fail-closed: if ANY candidate is unresolvable, the generator returns null for the
        // entire condition → rule appends FALSE (SmvMainModuleBuilder:402-406).
        // Must return false regardless of IN or NOT_IN to avoid false positives.
        for (String candidate : candidates) {
            if (!isResolvableStateCandidate(condSmv, candidate)) {
                return false;
            }
        }

        boolean matched = false;

        if (modeCount == 1) {
            // Single-mode: clean device state, clean each candidate, check membership
            String mode = condSmv.getModes().get(0);
            String modeState = getDeviceModeState(devTrace, condSmv, mode);
            String cleanDevice = DeviceSmvDataFactory.cleanStateName(
                    modeState != null ? modeState : devTrace.getState());
            for (String candidate : candidates) {
                String cleanCandidate = DeviceSmvDataFactory.cleanStateName(candidate);
                if (cleanDevice != null && cleanDevice.equals(cleanCandidate)) {
                    matched = true;
                    break;
                }
            }
        } else {
            // Multi-mode: each candidate may be a tuple ("cool;high") or a single state ("cool").
            for (String candidate : candidates) {
                if (candidate.contains(";")) {
                    if (matchesStateTuple(devTrace, condSmv, candidate)) {
                        matched = true;
                        break;
                    }
                } else if (matchesSingleStateCandidate(devTrace, condSmv, candidate)) {
                    matched = true;
                    break;
                }
            }
        }

        return "in".equals(relation) ? matched : !matched;
    }

    /**
     * Check if a state candidate can be resolved to a legal mode-state tuple.
     * Mirrors SmvMainModuleBuilder.resolveStateTupleCandidate(): returns true only if the
     * candidate would produce a non-null result. If false, the generator would fail-closed
     * the entire rule to FALSE.
     */
    private boolean isResolvableStateCandidate(DeviceSmvData condSmv, String candidate) {
        List<String> modes = condSmv.getModes();
        Map<String, List<String>> modeStates = condSmv.getModeStates();
        if (modeStates == null) return false;

        // Multi-mode tuple (contains ;)
        if (candidate.contains(";") && modes.size() > 1) {
            String[] segments = candidate.split(";", -1);
            if (segments.length != modes.size()) return false;
            boolean anyNonWildcard = false;
            for (int i = 0; i < modes.size(); i++) {
                String seg = segments[i].trim();
                if (seg.isEmpty()) continue; // wildcard
                anyNonWildcard = true;
                String cleanSeg = DeviceSmvDataFactory.cleanStateName(seg);
                List<String> legalStates = modeStates.get(modes.get(i));
                if (legalStates == null || !legalStates.contains(cleanSeg)) return false;
            }
            return anyNonWildcard; // all-wildcard → unresolvable (generator:697)
        }

        // Single value
        String cleanCandidate = DeviceSmvDataFactory.cleanStateName(candidate);
        if (cleanCandidate == null || cleanCandidate.isEmpty()) return false;

        if (modes.size() == 1) {
            // Single-mode: must exist in mode's state list (generator:698)
            List<String> legalStates = modeStates.get(modes.get(0));
            return legalStates != null && legalStates.contains(cleanCandidate);
        }

        // Multi-mode single value: must uniquely belong to exactly one mode (generator:713)
        int matchCount = 0;
        for (String mode : modes) {
            List<String> legalStates = modeStates.get(mode);
            if (legalStates != null && legalStates.contains(cleanCandidate)) {
                matchCount++;
            }
        }
        return matchCount == 1;
    }

    /**
     * Check if device state matches a multi-mode tuple candidate (e.g., "cool;high").
     * Mirrors SmvMainModuleBuilder.resolveStateTupleCandidate() semantics:
     * split by ';', compare per-mode, allow empty/wildcard segments.
     */
    private boolean matchesStateTuple(TraceDeviceDto devTrace, DeviceSmvData condSmv,
                                       String tupleCandidate) {
        List<String> modes = condSmv.getModes();
        String[] segments = tupleCandidate.split(";", -1);
        if (segments.length != modes.size()) return false;

        boolean anyNonWildcard = false;
        for (int i = 0; i < modes.size(); i++) {
            String candidateSeg = segments[i].trim();
            if (candidateSeg.isEmpty()) continue; // wildcard segment
            anyNonWildcard = true;

            String mode = modes.get(i);
            String deviceModeState = getDeviceModeState(devTrace, condSmv, mode);
            if (deviceModeState == null) return false;

            String cleanCandidate = DeviceSmvDataFactory.cleanStateName(candidateSeg);
            String cleanDevice = DeviceSmvDataFactory.cleanStateName(deviceModeState);
            if (!Objects.equals(cleanCandidate, cleanDevice)) {
                return false;
            }
        }
        // All-wildcard tuple is invalid (mirrors resolveStateTupleCandidate returning null)
        return anyNonWildcard;
    }

    /**
     * Check if a single (non-tuple) state value matches the device on exactly one mode.
     * Mirrors SmvMainModuleBuilder.resolveStateTupleCandidate() lines 690-718:
     * for multi-mode devices, a single value is valid only if it uniquely belongs to one mode.
     */
    private boolean matchesSingleStateCandidate(TraceDeviceDto devTrace, DeviceSmvData condSmv,
                                                 String candidate) {
        List<String> modes = condSmv.getModes();
        Map<String, List<String>> modeStates = condSmv.getModeStates();
        if (modeStates == null) return false;

        String cleanCandidate = DeviceSmvDataFactory.cleanStateName(candidate);
        if (cleanCandidate == null || cleanCandidate.isEmpty()) return false;

        // Find which mode(s) contain this state; must be exactly 1 (generator:713)
        String matchedMode = null;
        for (String mode : modes) {
            List<String> legalStates = modeStates.get(mode);
            if (legalStates != null && legalStates.contains(cleanCandidate)) {
                if (matchedMode != null) return false; // ambiguous: belongs to >1 mode
                matchedMode = mode;
            }
        }
        if (matchedMode == null) return false;

        // Compare the matched mode's device state
        String deviceModeState = getDeviceModeState(devTrace, condSmv, matchedMode);
        if (deviceModeState == null) return false;
        String cleanDevice = DeviceSmvDataFactory.cleanStateName(deviceModeState);
        return Objects.equals(cleanCandidate, cleanDevice);
    }

    // ===== Command effect checking =====

    private boolean checkStartState(DeviceManifest.API api, DeviceSmvData targetSmv,
                                    TraceStateDto currentState) {
        String startState = api.getStartState();
        if (startState == null || startState.isBlank()) return true; // no constraint

        TraceDeviceDto devTrace = findDeviceInState(currentState, targetSmv);
        if (devTrace == null) return false;

        String deviceState = devTrace.getState();
        if (deviceState == null) return true; // can't determine, be permissive

        String cleanStart = DeviceSmvDataFactory.cleanStateName(startState);
        String cleanDevice = DeviceSmvDataFactory.cleanStateName(deviceState);

        // Direct match
        if (cleanStart.equals(cleanDevice) || startState.equals(deviceState)) {
            return true;
        }

        // Multi-mode: startState may be for a specific mode (e.g. "HvacMode_cool")
        if (targetSmv.getModes() != null) {
            int modeIdx = DeviceSmvDataFactory.getModeIndexOfState(targetSmv, startState);
            if (modeIdx >= 0 && modeIdx < targetSmv.getModes().size()) {
                String mode = targetSmv.getModes().get(modeIdx);
                String currentModeState = getDeviceModeState(devTrace, targetSmv, mode);
                if (currentModeState != null) {
                    String perModeStart = extractModeState(startState, modeIdx);
                    if (perModeStart != null) {
                        String cleanPerMode = DeviceSmvDataFactory.cleanStateName(perModeStart);
                        String cleanCurrentMode = DeviceSmvDataFactory.cleanStateName(currentModeState);
                        return cleanPerMode.equals(cleanCurrentMode);
                    }
                }
            }
        }
        return false;
    }

    private boolean checkCommandEffect(DeviceManifest.API api, DeviceSmvData targetSmv,
                                       TraceStateDto currentState, TraceStateDto nextState) {
        String endState = api.getEndState();
        if (endState == null || endState.isBlank()) return true; // no end state defined

        TraceDeviceDto nextDevTrace = findDeviceInState(nextState, targetSmv);
        if (nextDevTrace == null) return false;

        String nextDeviceState = nextDevTrace.getState();
        if (nextDeviceState == null) return false;

        String cleanEnd = DeviceSmvDataFactory.cleanStateName(endState);
        String cleanNext = DeviceSmvDataFactory.cleanStateName(nextDeviceState);

        // Direct match
        if (cleanEnd.equals(cleanNext) || endState.equals(nextDeviceState)) {
            return true;
        }

        // For multi-mode: endState may be for a specific mode; check if that mode changed
        if (targetSmv.getModes() != null) {
            int modeIdx = DeviceSmvDataFactory.getModeIndexOfState(targetSmv, endState);
            if (modeIdx >= 0 && modeIdx < targetSmv.getModes().size()) {
                String mode = targetSmv.getModes().get(modeIdx);
                String nextModeState = getDeviceModeState(nextDevTrace, targetSmv, mode);
                if (nextModeState != null) {
                    String perModeEnd = extractModeState(endState, modeIdx);
                    if (perModeEnd != null) {
                        String cleanPerMode = DeviceSmvDataFactory.cleanStateName(perModeEnd);
                        String cleanNextMode = DeviceSmvDataFactory.cleanStateName(nextModeState);
                        if (cleanPerMode.equals(cleanNextMode)) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }

    // ===== Conflict detection =====

    private void detectConflicts(List<FaultRuleDto> stepTriggered, List<RuleDto> rules,
                                 Map<String, DeviceSmvData> deviceSmvMap) {
        for (int i = 0; i < stepTriggered.size(); i++) {
            FaultRuleDto a = stepTriggered.get(i);
            for (int j = i + 1; j < stepTriggered.size(); j++) {
                FaultRuleDto b = stepTriggered.get(j);
                if (!a.getTargetDevice().equals(b.getTargetDevice())) continue;

                // Same device, check if actions lead to different end states
                RuleDto ruleA = rules.get(a.getRuleIndex());
                RuleDto ruleB = rules.get(b.getRuleIndex());
                DeviceSmvData smv = findDevice(a.getTargetDevice(), deviceSmvMap);
                if (smv == null) continue;

                DeviceManifest.API apiA = DeviceSmvDataFactory.findApi(smv.getManifest(), ruleA.getCommand().getAction());
                DeviceManifest.API apiB = DeviceSmvDataFactory.findApi(smv.getManifest(), ruleB.getCommand().getAction());
                if (apiA == null || apiB == null) continue;

                String endA = apiA.getEndState();
                String endB = apiB.getEndState();
                if (endA != null && endB != null && !endA.equals(endB)) {
                    a.setConflicting(true);
                    a.setConflictWithRuleIndex(b.getRuleIndex());
                    a.setReason("Conflicts with rule " + b.getRuleIndex()
                            + ": both target " + a.getTargetDevice()
                            + " but with different end states (" + endA + " vs " + endB + ")");

                    b.setConflicting(true);
                    b.setConflictWithRuleIndex(a.getRuleIndex());
                    b.setReason("Conflicts with rule " + a.getRuleIndex()
                            + ": both target " + b.getTargetDevice()
                            + " but with different end states (" + endB + " vs " + endA + ")");
                }
            }
        }

        // Set default reason for non-conflicting triggered rules
        for (FaultRuleDto fault : stepTriggered) {
            if (fault.getReason() == null) {
                fault.setReason("Triggered at step " + fault.getTriggerStep()
                        + ": action " + fault.getTargetAction() + " on " + fault.getTargetDevice());
            }
        }
    }

    // ===== Helpers =====

    private DeviceSmvData findDevice(String deviceName, Map<String, DeviceSmvData> deviceSmvMap) {
        if (deviceName == null || deviceSmvMap == null) return null;
        try {
            return DeviceSmvDataFactory.findDeviceSmvDataStrict(deviceName, deviceSmvMap);
        } catch (Exception e) {
            log.debug("Device lookup failed for '{}': {}", deviceName, e.getMessage());
            return null;
        }
    }

    private TraceDeviceDto findDeviceInState(TraceStateDto state, DeviceSmvData smv) {
        if (state == null || state.getDevices() == null || smv == null) return null;
        String varName = smv.getVarName();
        String templateName = smv.getTemplateName();
        for (TraceDeviceDto dev : state.getDevices()) {
            if (dev.getDeviceId() == null) continue;
            if ((varName != null && dev.getDeviceId().equals(varName))
                    || (templateName != null && dev.getDeviceId().equals(templateName))) {
                return dev;
            }
        }
        return null;
    }

    private String getDeviceModeState(TraceDeviceDto devTrace, DeviceSmvData smv, String mode) {
        // The trace stores mode states directly in the device state field for single-mode devices
        if (smv.getModes() != null && smv.getModes().size() == 1) {
            return devTrace.getState();
        }
        // For multi-mode: state is semicolon-separated matching mode order
        if (devTrace.getState() != null && devTrace.getState().contains(";")) {
            String[] parts = devTrace.getState().split(";");
            int modeIdx = smv.getModes().indexOf(mode);
            if (modeIdx >= 0 && modeIdx < parts.length) {
                return parts[modeIdx].trim();
            }
        }
        return devTrace.getState();
    }

    private String getVariableValue(TraceDeviceDto devTrace, String varName) {
        if (devTrace.getVariables() == null) return null;
        for (TraceVariableDto v : devTrace.getVariables()) {
            if (varName.equals(v.getName())) return v.getValue();
        }
        return null;
    }

    private String extractModeState(String multiModeState, int modeIdx) {
        if (multiModeState == null) return null;
        String[] parts = multiModeState.split(";");
        if (parts.length == 1) {
            return multiModeState.trim(); // single-mode: return as-is
        }
        if (modeIdx >= 0 && modeIdx < parts.length) {
            return parts[modeIdx].trim();
        }
        return null; // index out of bounds for multi-mode state
    }

    private boolean compareValues(String actual, String relation, String expected) {
        if (actual == null || expected == null || relation == null) return false;

        String cleanActual = actual.trim();
        String cleanExpected = expected.trim().replace(" ", "");

        switch (relation.trim()) {
            case "=", "==" -> {
                return cleanActual.equals(cleanExpected);
            }
            case "!=", "<>" -> {
                return !cleanActual.equals(cleanExpected);
            }
            case ">", "<", ">=", "<=" -> {
                return compareNumeric(cleanActual, relation.trim(), cleanExpected);
            }
            case "in" -> {
                return parseValueSet(cleanExpected).contains(cleanActual);
            }
            case "not in" -> {
                return !parseValueSet(cleanExpected).contains(cleanActual);
            }
            default -> {
                return false;
            }
        }
    }

    private boolean compareNumeric(String actual, String relation, String expected) {
        try {
            double a = Double.parseDouble(actual);
            double e = Double.parseDouble(expected);
            return switch (relation) {
                case ">" -> a > e;
                case "<" -> a < e;
                case ">=" -> a >= e;
                case "<=" -> a <= e;
                default -> false;
            };
        } catch (NumberFormatException ex) {
            return false;
        }
    }

    private Set<String> parseValueSet(String value) {
        Set<String> set = new HashSet<>();
        // Remove braces/brackets if present (defensive, values normally don't have them)
        String cleaned = value.replaceAll("[{}\\[\\]()]", "").trim();
        // Split by [,;|] matching SmvRelationUtils.splitRuleValues() semantics
        for (String v : cleaned.split("[,;|]")) {
            String trimmed = v.trim();
            if (!trimmed.isEmpty()) set.add(trimmed);
        }
        return set;
    }
}
