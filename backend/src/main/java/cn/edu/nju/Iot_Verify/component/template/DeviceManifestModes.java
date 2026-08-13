package cn.edu.nju.Iot_Verify.component.template;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * Reads the mode / working-state structure out of a device manifest.
 *
 * <p>A manifest declares modes plus working states whose names encode one state per mode,
 * separated by {@code ;} (a single-mode template omits the separator). Both template validation
 * and board persistence need that decoding, so it lives here rather than being duplicated or
 * reached for across a service boundary.</p>
 */
public final class DeviceManifestModes {

    private DeviceManifestModes() {
    }

    private static boolean hasText(String value) {
        return value != null && !value.isBlank();
    }

    /** Declared mode names, trimmed, with blanks dropped. */
    public static List<String> modeNames(DeviceManifest manifest) {
        if (manifest == null || manifest.getModes() == null) {
            return List.of();
        }
        return manifest.getModes().stream()
                .filter(DeviceManifestModes::hasText)
                .map(String::trim)
                .toList();
    }

    /** Mode name to the distinct states that mode can take, in declaration order. */
    public static Map<String, List<String>> modeStates(DeviceManifest manifest) {
        List<String> modes = modeNames(manifest);
        if (modes.isEmpty() || manifest == null || manifest.getWorkingStates() == null) {
            return Collections.emptyMap();
        }
        Map<String, List<String>> result = new LinkedHashMap<>();
        for (String mode : modes) {
            result.put(mode, new ArrayList<>());
        }

        boolean singleMode = modes.size() == 1;
        for (DeviceManifest.WorkingState state : manifest.getWorkingStates()) {
            if (state == null || !hasText(state.getName())) {
                continue;
            }
            if (singleMode) {
                addUniqueState(result.get(modes.get(0)), DeviceSmvDataFactory.cleanStateName(state.getName()));
                continue;
            }
            String[] parts = state.getName().split(";");
            for (int i = 0; i < parts.length && i < modes.size(); i++) {
                addUniqueState(result.get(modes.get(i)), DeviceSmvDataFactory.cleanStateName(parts[i]));
            }
        }
        return result;
    }

    private static void addUniqueState(List<String> states, String state) {
        if (states != null && hasText(state) && !states.contains(state)) {
            states.add(state);
        }
    }

    /**
     * The value a device-local enum variable holds in {@code state}, if that state declares one.
     *
     * <p>A WorkingState's {@code Dynamics} entry is not an action but a standing constraint: the generator
     * emits it as a branch of {@code next(<device>.<var>)} guarded by being in that state. So the state a
     * device starts in already determines such a variable's initial value, and defaulting it independently
     * to {@code Values[0]} produced a step-0 model that contradicts itself — {@code init(CarLocation) := away}
     * beside {@code init(location) := garage}, on six bundled templates. This is the one place that
     * derivation lives; every defaulter calls it rather than re-deriving.</p>
     *
     * <p>Enum only, deliberately. A numeric target declares {@code ChangeRate}, a rate that says nothing
     * about the current value (schema {@code oneOf} makes the two exclusive), so there is nothing to derive
     * and a numeric local keeps its lower-bound default. Returns {@code null} when the state declares no
     * {@code Value} for the variable, which means "no opinion", not "empty".</p>
     */
    public static String stateDeclaredValue(DeviceManifest manifest, String stateName, String variableName) {
        if (manifest == null || !hasText(stateName) || !hasText(variableName)
                || manifest.getWorkingStates() == null) {
            return null;
        }
        // A Transition assignment on the same variable means the state does not determine it: the generator
        // emits transition branches ahead of the state branches in one `case`, and first match wins, so a
        // firing transition overrides the state's Dynamics. Treating such a variable as state-determined
        // would default it wrongly and make the writer gates refuse a pair the transition legitimately
        // produces. No bundled template does this — Clock's only assignment targets a shared variable — so
        // this guards custom templates.
        if (isDrivenByTransition(manifest, variableName)) {
            return null;
        }
        String wanted = stateName.trim();
        for (DeviceManifest.WorkingState state : manifest.getWorkingStates()) {
            if (state == null || state.getName() == null || state.getDynamics() == null) {
                continue;
            }
            // Match the complete tuple: a multi-mode InitState like `heating;ready` names one WorkingState,
            // and matching a single segment would pick an arbitrary sibling.
            if (!wanted.equals(state.getName().trim())) {
                continue;
            }
            for (DeviceManifest.Dynamic dynamic : state.getDynamics()) {
                if (dynamic == null || !variableName.equals(dynamic.getVariableName())) {
                    continue;
                }
                return hasText(dynamic.getValue()) ? dynamic.getValue().trim() : null;
            }
        }
        return null;
    }


    /** Whether a Transition assignment targets this variable, making it more than the state's consequence. */
    private static boolean isDrivenByTransition(DeviceManifest manifest, String variableName) {
        if (manifest.getTransitions() == null) {
            return false;
        }
        for (DeviceManifest.Transition transition : manifest.getTransitions()) {
            if (transition == null || transition.getAssignments() == null) {
                continue;
            }
            for (DeviceManifest.Assignment assignment : transition.getAssignments()) {
                if (assignment != null && variableName.equals(assignment.getAttribute())) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * A device-local variable's initial value for a device starting in {@code stateName}: the value that
     * state declares, else the documented template default (first enum literal, or the lower bound).
     *
     * <p>{@code stateName} is the device's own starting state, not necessarily the template's
     * {@code InitState} — a user who sets a car's state to {@code garage} means its location to read
     * {@code garage}. {@code FuzzModel} already resolves its initial state that way.</p>
     */
    public static String localInitialValue(DeviceManifest manifest,
                                          DeviceManifest.InternalVariable variable,
                                          String stateName) {
        if (variable == null || variable.getName() == null) {
            return null;
        }
        String declared = stateDeclaredValue(manifest, stateName, variable.getName());
        if (declared != null) {
            return declared;
        }
        if (variable.getValues() != null && !variable.getValues().isEmpty()) {
            return variable.getValues().get(0);
        }
        if (variable.getLowerBound() != null && variable.getUpperBound() != null) {
            return String.valueOf(variable.getLowerBound());
        }
        return null;
    }
}
