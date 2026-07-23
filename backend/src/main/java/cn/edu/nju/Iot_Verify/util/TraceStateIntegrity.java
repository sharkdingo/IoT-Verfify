package cn.edu.nju.Iot_Verify.util;

import cn.edu.nju.Iot_Verify.dto.model.ModelTokenSource;
import cn.edu.nju.Iot_Verify.dto.trace.TraceDeviceDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceVariableDto;

import java.util.List;

/** Minimal structural contract required by trace playback clients. */
public final class TraceStateIntegrity {

    private TraceStateIntegrity() {
    }

    public static List<TraceStateDto> requireValidStates(List<TraceStateDto> states) {
        if (states == null) throw new IllegalArgumentException("Trace state list is missing");
        for (int index = 0; index < states.size(); index++) {
            requireValidState(states.get(index), index + 1);
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
        requireNoNullElements(state.getDevices(), "Trace state devices list");
        state.setTriggeredRules(normalizeLegacyList(
                state.getTriggeredRules(), "Trace state triggered rules list"));
        state.setCompromisedAutomationLinks(normalizeLegacyList(
                state.getCompromisedAutomationLinks(), "Trace state compromised links list"));
        requireNoNullElementsIfPresent(state.getTrustPrivacies(), "Trace state trust/privacy list");
        requireNoNullElementsIfPresent(state.getEnvVariables(), "Trace environment variables list");
        requireNoNullElementsIfPresent(state.getGlobalVariables(), "Trace global variables list");
        state.getDevices().forEach(TraceStateIntegrity::requireValidDevice);
        requireValidVariablesIfPresent(state.getEnvVariables());
        requireValidVariablesIfPresent(state.getGlobalVariables());
    }

    /** Validates a formal trace element while it is read from an ordered JSON array. */
    public static void requireValidState(TraceStateDto state, int expectedStateIndex) {
        requireValidState(state);
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
            device.setModelTokenSource(ModelTokenSource.UNKNOWN);
        }
        requireNoNullElements(device.getVariables(), "Trace device variables list");
        device.getVariables().forEach(TraceStateIntegrity::requireValidVariable);
        requireNoNullElementsIfPresent(device.getTrustPrivacy(), "Trace device trust labels list");
        requireNoNullElementsIfPresent(device.getPrivacies(), "Trace device privacy labels list");
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

    private static void requireValidVariablesIfPresent(List<TraceVariableDto> variables) {
        if (variables != null) variables.forEach(TraceStateIntegrity::requireValidVariable);
    }

    private static void requireValidVariable(TraceVariableDto variable) {
        if (variable == null) throw new IllegalArgumentException("Trace variable is null");
        requireNonBlank(variable.getName(), "Trace variable name");
        if (variable.getValue() == null) {
            throw new IllegalArgumentException("Trace variable value is missing");
        }
        if (variable.getModelTokenSource() == null) {
            variable.setModelTokenSource(ModelTokenSource.UNKNOWN);
        }
    }

    private static <T> List<T> normalizeLegacyList(List<T> values, String field) {
        if (values == null) return List.of();
        requireNoNullElements(values, field);
        return values;
    }
}
