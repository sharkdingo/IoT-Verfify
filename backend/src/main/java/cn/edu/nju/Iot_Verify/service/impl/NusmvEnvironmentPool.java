package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvDataFactory;
import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.device.PrivacyStateDto;
import cn.edu.nju.Iot_Verify.dto.device.VariableStateDto;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.TreeMap;

final class NusmvEnvironmentPool {

    private NusmvEnvironmentPool() {
    }

    static List<BoardEnvironmentVariableDto> mergeWithDefaults(
            List<BoardEnvironmentVariableDto> submitted,
            Map<String, DeviceSmvData> deviceSmvMap) {
        Map<String, DeviceManifest.InternalVariable> required = collectRequired(deviceSmvMap);
        Map<String, BoardEnvironmentVariableDto> submittedByName = toMap(submitted);
        List<BoardEnvironmentVariableDto> result = new ArrayList<>();

        for (Map.Entry<String, DeviceManifest.InternalVariable> entry : required.entrySet()) {
            String name = entry.getKey();
            DeviceManifest.InternalVariable definition = entry.getValue();
            BoardEnvironmentVariableDto submittedValue = submittedByName.remove(name);
            String value = submittedValue != null ? trimToNull(submittedValue.getValue()) : null;
            if (value == null) {
                value = defaultValue(definition);
            }
            String trust = submittedValue != null ? submittedValue.getTrust() : definition.getTrust();
            String privacy = submittedValue != null ? submittedValue.getPrivacy() : definition.getPrivacy();
            result.add(new BoardEnvironmentVariableDto(
                    name,
                    value,
                    normalizeTrustPrivacy(trust, normalizeTrustPrivacy(definition.getTrust(), "untrusted")),
                    normalizeTrustPrivacy(privacy, normalizeTrustPrivacy(definition.getPrivacy(), "public"))
            ));
        }

        // Preserve unknown submitted variables so request validation can report them explicitly.
        result.addAll(submittedByName.values());
        return result;
    }

    static List<DeviceVerificationDto> expandDevices(
            List<DeviceVerificationDto> devices,
            List<BoardEnvironmentVariableDto> environmentVariables,
            Map<String, DeviceSmvData> deviceSmvMap) {
        Map<String, BoardEnvironmentVariableDto> environmentByName = toMap(environmentVariables);
        List<DeviceVerificationDto> expanded = new ArrayList<>();
        if (devices == null) {
            return expanded;
        }

        for (DeviceVerificationDto device : devices) {
            if (device == null) {
                continue;
            }
            DeviceVerificationDto copy = copyDevice(device);
            DeviceSmvData smv = smvForDevice(device, deviceSmvMap);
            if (smv == null) {
                expanded.add(copy);
                continue;
            }

            Map<String, VariableStateDto> variables = variableMap(copy.getVariables());
            Map<String, PrivacyStateDto> privacies = privacyMap(copy.getPrivacies());
            Set<String> environmentNames = new LinkedHashSet<>();
            if (smv.getEnvVariables() != null) {
                environmentNames.addAll(smv.getEnvVariables().keySet());
            }

            for (String name : environmentNames) {
                BoardEnvironmentVariableDto environment = environmentByName.get(name);
                if (environment == null) {
                    continue;
                }
                String value = trimToNull(environment.getValue());
                String trust = trimToNull(environment.getTrust());
                if (value != null || trust != null) {
                    variables.put(name, new VariableStateDto(name, value, trust));
                }
                String privacy = trimToNull(environment.getPrivacy());
                if (privacy != null) {
                    privacies.put(name, new PrivacyStateDto(name, privacy));
                }
            }
            copy.setVariables(variables.isEmpty() ? null : new ArrayList<>(variables.values()));
            copy.setPrivacies(privacies.isEmpty() ? null : new ArrayList<>(privacies.values()));
            expanded.add(copy);
        }
        return expanded;
    }

    static Map<String, DeviceManifest.InternalVariable> collectRequired(Map<String, DeviceSmvData> deviceSmvMap) {
        Map<String, DeviceManifest.InternalVariable> required = new TreeMap<>();
        if (deviceSmvMap == null || deviceSmvMap.isEmpty()) {
            return required;
        }
        for (Map.Entry<String, DeviceSmvData> entry : deviceSmvMap.entrySet()) {
            DeviceSmvData smv = entry.getValue();
            if (smv == null) {
                continue;
            }
            if (!Objects.equals(entry.getKey(), smv.getVarName())) {
                continue;
            }
            if (smv.getEnvVariables() != null) {
                for (Map.Entry<String, DeviceManifest.InternalVariable> env : smv.getEnvVariables().entrySet()) {
                    if (env.getKey() != null && env.getValue() != null) {
                        required.putIfAbsent(env.getKey(), env.getValue());
                    }
                }
            }
            if (smv.getImpactedEnvironmentVariables() != null) {
                for (Map.Entry<String, DeviceManifest.InternalVariable> env : smv.getImpactedEnvironmentVariables().entrySet()) {
                    if (env.getKey() != null && env.getValue() != null) {
                        required.putIfAbsent(env.getKey(), env.getValue());
                    }
                }
            }
        }
        return required;
    }

    static String defaultValue(DeviceManifest.InternalVariable variable) {
        if (variable == null) {
            return null;
        }
        if (variable.getValues() != null && !variable.getValues().isEmpty()) {
            return trimToNull(variable.getValues().get(0));
        }
        if (variable.getLowerBound() != null && variable.getUpperBound() != null) {
            return String.valueOf(variable.getLowerBound());
        }
        return null;
    }

    private static DeviceVerificationDto copyDevice(DeviceVerificationDto source) {
        DeviceVerificationDto copy = new DeviceVerificationDto();
        copy.setVarName(source.getVarName());
        copy.setDeviceLabel(source.getDeviceLabel());
        copy.setTemplateName(source.getTemplateName());
        copy.setState(source.getState());
        copy.setCurrentStateTrust(source.getCurrentStateTrust());
        copy.setCurrentStatePrivacy(source.getCurrentStatePrivacy());
        copy.setVariables(source.getVariables() == null ? null : new ArrayList<>(source.getVariables()));
        copy.setPrivacies(source.getPrivacies() == null ? null : new ArrayList<>(source.getPrivacies()));
        return copy;
    }

    private static DeviceSmvData smvForDevice(DeviceVerificationDto device, Map<String, DeviceSmvData> deviceSmvMap) {
        if (device == null || deviceSmvMap == null) {
            return null;
        }
        DeviceSmvData smv = deviceSmvMap.get(device.getVarName());
        if (smv != null) {
            return smv;
        }
        return DeviceSmvDataFactory.findDeviceSmvDataStrict(device.getVarName(), deviceSmvMap);
    }

    private static Map<String, BoardEnvironmentVariableDto> toMap(List<BoardEnvironmentVariableDto> variables) {
        Map<String, BoardEnvironmentVariableDto> result = new LinkedHashMap<>();
        if (variables == null) {
            return result;
        }
        for (BoardEnvironmentVariableDto variable : variables) {
            if (variable == null || trimToNull(variable.getName()) == null) {
                continue;
            }
            String name = trimToNull(variable.getName());
            result.putIfAbsent(name, new BoardEnvironmentVariableDto(
                    name,
                    trimToNull(variable.getValue()),
                    trimToNull(variable.getTrust()),
                    trimToNull(variable.getPrivacy())
            ));
        }
        return result;
    }

    private static Map<String, VariableStateDto> variableMap(List<VariableStateDto> values) {
        Map<String, VariableStateDto> result = new LinkedHashMap<>();
        if (values == null) {
            return result;
        }
        for (VariableStateDto value : values) {
            if (value != null && trimToNull(value.getName()) != null) {
                result.put(value.getName().trim(), value);
            }
        }
        return result;
    }

    private static Map<String, PrivacyStateDto> privacyMap(List<PrivacyStateDto> values) {
        Map<String, PrivacyStateDto> result = new LinkedHashMap<>();
        if (values == null) {
            return result;
        }
        for (PrivacyStateDto value : values) {
            if (value != null && trimToNull(value.getName()) != null) {
                result.put(value.getName().trim(), value);
            }
        }
        return result;
    }

    private static String normalizeTrustPrivacy(String value, String fallback) {
        String normalized = DeviceSmvDataFactory.normalizeTrustPrivacy(value);
        return normalized != null ? normalized : fallback;
    }

    private static String trimToNull(String value) {
        if (value == null) {
            return null;
        }
        String trimmed = value.trim();
        return trimmed.isEmpty() ? null : trimmed;
    }
}
