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
}
