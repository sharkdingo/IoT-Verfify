package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.model.ModelTokenSource;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDeviceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceTrustPrivacyDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceTriggeredRuleDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceVariableDto;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** Structural contract shared by every persisted trace producer and playback client. */
public final class TraceStateIntegrity {

    private TraceStateIntegrity() {
    }

    public static List<TraceStateDto> requireValidStates(List<TraceStateDto> states) {
        return requireValidStates(states, 1);
    }

    /**
     * Validates an ordered trace using the producer's documented state-index convention.
     * Formal and simulation traces are one-based; fuzz findings are zero-based.
     */
    public static List<TraceStateDto> requireValidStates(
            List<TraceStateDto> states, int firstStateIndex) {
        if (states == null) throw new IllegalArgumentException("Trace state list is missing");
        if (firstStateIndex != 0 && firstStateIndex != 1) {
            throw new IllegalArgumentException("Trace first state index must be zero or one");
        }

        Map<String, FrozenDeviceIdentity> frozenDevices = new LinkedHashMap<>();
        Set<String> frozenDeviceIds = null;
        Map<String, Set<String>> frozenDeviceVariableNames = new LinkedHashMap<>();
        Map<String, ModelTokenSource> frozenEnvironmentSources = new LinkedHashMap<>();
        Set<String> frozenEnvironmentNames = null;
        Set<String> frozenGlobalNames = null;

        for (int index = 0; index < states.size(); index++) {
            TraceStateDto state = states.get(index);
            requireValidState(state, firstStateIndex + index);

            Set<String> deviceIds = new HashSet<>();
            for (TraceDeviceDto device : state.getDevices()) {
                deviceIds.add(device.getDeviceId());
                FrozenDeviceIdentity identity = new FrozenDeviceIdentity(
                        device.getDeviceLabel(), device.getTemplateName(),
                        device.getModelTokenSource());
                FrozenDeviceIdentity previousIdentity = frozenDevices.putIfAbsent(
                        device.getDeviceId(), identity);
                if (previousIdentity != null && !previousIdentity.equals(identity)) {
                    throw new IllegalArgumentException(
                            "Trace device identity and model token source changed across states");
                }

                Set<String> variableNames = variableNames(device.getVariables());
                Set<String> previousVariableNames = frozenDeviceVariableNames.putIfAbsent(
                        device.getDeviceId(), variableNames);
                if (previousVariableNames != null
                        && !previousVariableNames.equals(variableNames)) {
                    throw new IllegalArgumentException(
                            "Trace device variable names changed across states");
                }
            }
            if (frozenDeviceIds != null && !frozenDeviceIds.equals(deviceIds)) {
                throw new IllegalArgumentException("Trace device identities changed across states");
            }
            frozenDeviceIds = deviceIds;

            Set<String> environmentNames = variableNames(state.getEnvVariables());
            if (frozenEnvironmentNames != null
                    && !frozenEnvironmentNames.equals(environmentNames)) {
                throw new IllegalArgumentException(
                        "Trace environment variable names changed across states");
            }
            frozenEnvironmentNames = environmentNames;
            for (TraceVariableDto variable : safe(state.getEnvVariables())) {
                ModelTokenSource previousSource = frozenEnvironmentSources.putIfAbsent(
                        variable.getName(), variable.getModelTokenSource());
                if (previousSource != null && previousSource != variable.getModelTokenSource()) {
                    throw new IllegalArgumentException(
                            "Trace environment variable model token source changed across states");
                }
            }

            Set<String> globalNames = variableNames(state.getGlobalVariables());
            if (frozenGlobalNames != null && !frozenGlobalNames.equals(globalNames)) {
                throw new IllegalArgumentException("Trace global variable names changed across states");
            }
            frozenGlobalNames = globalNames;
        }
        return states;
    }

    public static void requireValidState(TraceStateDto state) {
        if (state == null) throw new IllegalArgumentException("Trace state is null");
        if (state.getStateIndex() == null) {
            throw new IllegalArgumentException("Trace state index is missing");
        }
        if (state.getStateIndex() < 1) {
            throw new IllegalArgumentException("Trace state index must be one-based");
        }
        requireValidStateShape(state);
    }

    private static void requireValidStateShape(TraceStateDto state) {
        requireNoNullElements(state.getDevices(), "Trace state devices list");
        requireValidRuleEvidence(state);
        requireNoNullElementsIfPresent(state.getTrustPrivacies(), "Trace state trust/privacy list");
        requireNoNullElementsIfPresent(state.getEnvVariables(), "Trace environment variables list");
        requireNoNullElementsIfPresent(state.getGlobalVariables(), "Trace global variables list");
        state.getDevices().forEach(TraceStateIntegrity::requireValidDevice);
        requireUniqueDeviceIds(state.getDevices());
        requireValidTrustPrivacyList(
                state.getTrustPrivacies(), "Trace state trust/privacy list", EvidenceKind.EITHER);
        requireValidVariablesIfPresent(
                state.getEnvVariables(), "Trace environment variables list", null);
        requireValidVariablesIfPresent(
                state.getGlobalVariables(), "Trace global variables list", ModelTokenSource.UNKNOWN);
    }

    /** Validates rule evidence independently of the producer's state-index convention. */
    public static void requireValidRuleEvidence(TraceStateDto state) {
        if (state == null) throw new IllegalArgumentException("Trace state is null");
        requireNoNullElements(state.getTriggeredRules(), "Trace state triggered rules list");
        requireNoNullElements(
                state.getCompromisedAutomationLinks(), "Trace state compromised links list");
        requireValidRuleSnapshots(state.getTriggeredRules(), "Trace state triggered rules list");
        requireValidRuleSnapshots(
                state.getCompromisedAutomationLinks(), "Trace state compromised links list");
    }

    /** Validates the immutable rule list retained with a persisted run. */
    public static List<RuleDto> requireFrozenRules(List<RuleDto> rules, int expectedRuleCount) {
        if (rules == null) throw new IllegalArgumentException("Frozen rule list is missing");
        if (expectedRuleCount < 0 || rules.size() != expectedRuleCount) {
            throw new IllegalArgumentException("Frozen rule count does not match the model snapshot");
        }
        if (rules.stream().anyMatch(rule -> rule == null)) {
            throw new IllegalArgumentException("Frozen rule list contains null");
        }
        return rules;
    }

    /** Binds every persisted rule event to the exact rule submitted for that run. */
    public static void requireRuleEvidenceMatchesFrozenRules(
            List<TraceStateDto> states, List<RuleDto> frozenRules) {
        if (states == null) throw new IllegalArgumentException("Trace state list is missing");
        if (frozenRules == null) throw new IllegalArgumentException("Frozen rule list is missing");
        for (TraceStateDto state : states) {
            requireValidRuleEvidence(state);
            requireRuleSnapshotsMatch(
                    state.getTriggeredRules(), frozenRules, "Trace state triggered rules list");
            requireRuleSnapshotsMatch(
                    state.getCompromisedAutomationLinks(), frozenRules,
                    "Trace state compromised links list");
        }
    }

    /** Validates a trace element while it is read from an ordered JSON array. */
    public static void requireValidState(TraceStateDto state, int expectedStateIndex) {
        if (state == null) throw new IllegalArgumentException("Trace state is null");
        if (state.getStateIndex() == null) {
            throw new IllegalArgumentException("Trace state index is missing");
        }
        if (expectedStateIndex < 0) {
            throw new IllegalArgumentException("Expected trace state index cannot be negative");
        }
        requireValidStateShape(state);
        if (state.getStateIndex() != expectedStateIndex) {
            throw new IllegalArgumentException(
                    "Trace state index must be " + expectedStateIndex + " but was " + state.getStateIndex());
        }
    }

    private static void requireValidDevice(TraceDeviceDto device) {
        if (device == null) throw new IllegalArgumentException("Trace device is null");
        requireNonBlank(device.getDeviceId(), "Trace device id");
        requireNonBlank(device.getDeviceLabel(), "Trace device label");
        requireNonBlank(device.getTemplateName(), "Trace device template name");
        if (device.getModelTokenSource() == null) {
            throw new IllegalArgumentException("Trace device model token source is missing");
        }
        requireNoNullElements(device.getVariables(), "Trace device variables list");
        requireValidVariables(
                device.getVariables(), "Trace device variables list", device.getModelTokenSource());
        requireNoNullElementsIfPresent(device.getTrustPrivacy(), "Trace device trust labels list");
        requireNoNullElementsIfPresent(device.getPrivacies(), "Trace device privacy labels list");
        requireValidTrustPrivacyList(
                device.getTrustPrivacy(), "Trace device trust labels list", EvidenceKind.TRUST);
        requireValidTrustPrivacyList(
                device.getPrivacies(), "Trace device privacy labels list", EvidenceKind.PRIVACY);
    }

    private static void requireNoNullElements(List<?> values, String field) {
        if (values == null) throw new IllegalArgumentException(field + " is missing");
        if (values.stream().anyMatch(value -> value == null)) {
            throw new IllegalArgumentException(field + " contains null");
        }
    }

    private static void requireNoNullElementsIfPresent(List<?> values, String field) {
        if (values != null && values.stream().anyMatch(value -> value == null)) {
            throw new IllegalArgumentException(field + " contains null");
        }
    }

    private static void requireNonBlank(String value, String field) {
        if (value == null || value.isBlank()) {
            throw new IllegalArgumentException(field + " is missing");
        }
    }

    private static void requireValidVariablesIfPresent(
            List<TraceVariableDto> variables, String field, ModelTokenSource requiredSource) {
        if (variables != null) requireValidVariables(variables, field, requiredSource);
    }

    private static void requireValidVariables(
            List<TraceVariableDto> variables, String field, ModelTokenSource requiredSource) {
        Set<String> names = new HashSet<>();
        for (TraceVariableDto variable : variables) {
            requireValidVariable(variable);
            if (!names.add(variable.getName())) {
                throw new IllegalArgumentException(field + " contains a duplicate variable name");
            }
            if (requiredSource != null && variable.getModelTokenSource() != requiredSource) {
                throw new IllegalArgumentException(field + " contains an invalid model token source");
            }
        }
    }

    private static void requireValidRuleSnapshots(
            List<TraceTriggeredRuleDto> rules, String field) {
        Set<Integer> indexes = new HashSet<>();
        for (TraceTriggeredRuleDto rule : rules) {
            Integer ruleIndex = rule.getRuleIndex();
            if (ruleIndex == null || ruleIndex < 0) {
                throw new IllegalArgumentException(field + " contains an invalid rule index");
            }
            if (!indexes.add(ruleIndex)) {
                throw new IllegalArgumentException(field + " contains a duplicate rule index");
            }
            if (rule.getRuleId() != null && rule.getRuleId().isBlank()) {
                throw new IllegalArgumentException(field + " contains a blank rule id");
            }
        }
    }

    private static void requireRuleSnapshotsMatch(
            List<TraceTriggeredRuleDto> snapshots, List<RuleDto> frozenRules, String field) {
        for (TraceTriggeredRuleDto snapshot : snapshots) {
            int ruleIndex = snapshot.getRuleIndex();
            if (ruleIndex >= frozenRules.size()) {
                throw new IllegalArgumentException(field + " contains an out-of-range rule index");
            }
            RuleDto frozenRule = frozenRules.get(ruleIndex);
            String expectedId = frozenRule.getId() == null ? null : frozenRule.getId().toString();
            String expectedLabel = frozenRule.getRuleString();
            if (expectedLabel != null && expectedLabel.isBlank()) expectedLabel = null;
            if (!java.util.Objects.equals(snapshot.getRuleId(), expectedId)
                    || !java.util.Objects.equals(snapshot.getRuleLabel(), expectedLabel)) {
                throw new IllegalArgumentException(field + " does not match the frozen rule snapshot");
            }
        }
    }

    private static void requireValidVariable(TraceVariableDto variable) {
        if (variable == null) throw new IllegalArgumentException("Trace variable is null");
        requireNonBlank(variable.getName(), "Trace variable name");
        if (variable.getValue() == null) {
            throw new IllegalArgumentException("Trace variable value is missing");
        }
        if (variable.getModelTokenSource() == null) {
            throw new IllegalArgumentException("Trace variable model token source is missing");
        }
        if (variable.getTrust() != null
                && !"trusted".equals(variable.getTrust())
                && !"untrusted".equals(variable.getTrust())) {
            throw new IllegalArgumentException("Trace variable trust value is invalid");
        }
    }

    private static void requireUniqueDeviceIds(List<TraceDeviceDto> devices) {
        Set<String> ids = new HashSet<>();
        for (TraceDeviceDto device : devices) {
            if (!ids.add(device.getDeviceId())) {
                throw new IllegalArgumentException("Trace state devices list contains a duplicate device id");
            }
        }
    }

    private static void requireValidTrustPrivacyList(
            List<TraceTrustPrivacyDto> entries, String field, EvidenceKind evidenceKind) {
        if (entries == null) return;
        Set<TrustPrivacyIdentity> identities = new HashSet<>();
        for (TraceTrustPrivacyDto entry : entries) {
            requireNonBlank(entry.getName(), field + " entry name");
            String scope = entry.getPropertyScope();
            if (!"state".equals(scope) && !"variable".equals(scope) && !"content".equals(scope)) {
                throw new IllegalArgumentException(field + " contains an invalid property scope");
            }
            boolean stateScoped = "state".equals(scope);
            if ((stateScoped && (entry.getMode() == null || entry.getMode().isBlank()))
                    || (!stateScoped && entry.getMode() != null)) {
                throw new IllegalArgumentException(
                        field + " entry mode must be present only for state scope");
            }
            boolean hasTrust = entry.getTrust() != null;
            boolean hasPrivacy = entry.getPrivacy() != null;
            if (hasPrivacy
                    && !"private".equals(entry.getPrivacy())
                    && !"public".equals(entry.getPrivacy())) {
                throw new IllegalArgumentException(field + " contains an invalid privacy value");
            }
            if (evidenceKind == EvidenceKind.TRUST && (!hasTrust || hasPrivacy)) {
                throw new IllegalArgumentException(field + " must contain trust evidence only");
            }
            if (evidenceKind == EvidenceKind.PRIVACY && (!hasPrivacy || hasTrust)) {
                throw new IllegalArgumentException(field + " must contain privacy evidence only");
            }
            if (evidenceKind == EvidenceKind.EITHER && !hasTrust && !hasPrivacy) {
                throw new IllegalArgumentException(field + " entry has no trust or privacy evidence");
            }
            TrustPrivacyIdentity identity = new TrustPrivacyIdentity(
                    scope, entry.getMode(), entry.getName());
            if (!identities.add(identity)) {
                throw new IllegalArgumentException(field + " contains a duplicate property identity");
            }
        }
    }

    private static Set<String> variableNames(List<TraceVariableDto> variables) {
        Set<String> names = new HashSet<>();
        for (TraceVariableDto variable : safe(variables)) names.add(variable.getName());
        return names;
    }

    private static <T> List<T> safe(List<T> values) {
        return values == null ? List.of() : values;
    }

    private enum EvidenceKind {
        TRUST,
        PRIVACY,
        EITHER
    }

    private record FrozenDeviceIdentity(
            String deviceLabel, String templateName, ModelTokenSource modelTokenSource) {}

    private record TrustPrivacyIdentity(String propertyScope, String mode, String name) {}
}
