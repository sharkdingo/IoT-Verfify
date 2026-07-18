package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** The compromise choices that can actually change behavior in the generated model. */
public record AttackSurface(Set<String> deviceVarNames,
                            int automationLinkCount,
                            Set<String> falsifiableReadingDeviceVarNames,
                            Set<String> commandTargetDeviceVarNames,
                            Map<String, String> deviceDisplayLabels,
                            Map<Long, String> automationLinkDisplayLabels) {

    public AttackSurface {
        deviceVarNames = Collections.unmodifiableSet(new LinkedHashSet<>(
                deviceVarNames == null ? Set.of() : deviceVarNames));
        automationLinkCount = Math.max(0, automationLinkCount);
        Set<String> safeFalsifiableDevices = new LinkedHashSet<>(
                falsifiableReadingDeviceVarNames == null ? Set.of() : falsifiableReadingDeviceVarNames);
        safeFalsifiableDevices.retainAll(deviceVarNames);
        falsifiableReadingDeviceVarNames = Collections.unmodifiableSet(safeFalsifiableDevices);
        Set<String> safeCommandTargets = new LinkedHashSet<>(
                commandTargetDeviceVarNames == null ? Set.of() : commandTargetDeviceVarNames);
        safeCommandTargets.retainAll(deviceVarNames);
        commandTargetDeviceVarNames = Collections.unmodifiableSet(safeCommandTargets);
        Map<String, String> safeDeviceLabels = new LinkedHashMap<>();
        if (deviceDisplayLabels != null) {
            for (Map.Entry<String, String> entry : deviceDisplayLabels.entrySet()) {
                String id = entry.getKey();
                String label = entry.getValue();
                if (id != null && deviceVarNames.contains(id) && label != null && !label.isBlank()) {
                    safeDeviceLabels.put(id, label.trim());
                }
            }
        }
        deviceDisplayLabels = Collections.unmodifiableMap(safeDeviceLabels);
        Map<Long, String> safeLinkLabels = new LinkedHashMap<>();
        if (automationLinkDisplayLabels != null) {
            for (Map.Entry<Long, String> entry : automationLinkDisplayLabels.entrySet()) {
                Long id = entry.getKey();
                String label = entry.getValue();
                if (id != null && id > 0 && label != null && !label.isBlank()) {
                    safeLinkLabels.put(id, label.trim());
                }
            }
        }
        automationLinkDisplayLabels = Collections.unmodifiableMap(safeLinkLabels);
    }

    public AttackSurface(Set<String> deviceVarNames,
                         int automationLinkCount,
                         Set<String> falsifiableReadingDeviceVarNames,
                         Set<String> commandTargetDeviceVarNames) {
        this(deviceVarNames, automationLinkCount, falsifiableReadingDeviceVarNames,
                commandTargetDeviceVarNames, Map.of(), Map.of());
    }

    public AttackSurface(Set<String> deviceVarNames,
                         int automationLinkCount,
                         int falsifiableReadingDeviceCount) {
        this(deviceVarNames, automationLinkCount,
                firstDevices(deviceVarNames, falsifiableReadingDeviceCount), Set.of(), Map.of(), Map.of());
    }

    public int deviceCount() {
        return deviceVarNames.size();
    }

    public int totalCount() {
        return deviceCount() + automationLinkCount;
    }

    public boolean includesDevice(String varName) {
        return varName != null && deviceVarNames.contains(varName);
    }

    public boolean includesFalsifiableReadingDevice(String varName) {
        return varName != null && falsifiableReadingDeviceVarNames.contains(varName);
    }

    public boolean includesCommandTargetDevice(String varName) {
        return varName != null && commandTargetDeviceVarNames.contains(varName);
    }

    public int falsifiableReadingDeviceCount() {
        return falsifiableReadingDeviceVarNames.size();
    }

    public boolean hasFalsifiableReadingEffect() {
        return !falsifiableReadingDeviceVarNames.isEmpty();
    }

    public static AttackSurface analyze(List<RuleDto> rules, Map<String, DeviceSmvData> deviceSmvMap) {
        Set<String> effectfulDevices = new LinkedHashSet<>();
        Set<String> falsifiableReadingDevices = new LinkedHashSet<>();
        Set<String> commandTargetDevices = new LinkedHashSet<>();
        Map<String, String> deviceLabels = new LinkedHashMap<>();
        Map<Long, String> linkLabels = new LinkedHashMap<>();

        if (deviceSmvMap != null) {
            for (DeviceSmvData smv : deviceSmvMap.values()) {
                if (smv == null || smv.getVariables() == null) {
                    continue;
                }
                boolean hasFalsifiableReading = smv.getVariables().stream()
                        .anyMatch(variable -> variable != null
                                && Boolean.TRUE.equals(variable.getFalsifiableWhenCompromised()));
                if (hasFalsifiableReading && smv.getVarName() != null && !smv.getVarName().isBlank()) {
                    String canonicalVarName = smv.getVarName().trim();
                    falsifiableReadingDevices.add(canonicalVarName);
                    effectfulDevices.add(canonicalVarName);
                    putLabel(deviceLabels, canonicalVarName, smv.getDeviceLabel());
                }
            }
        }

        int linkCount = rules == null ? 0 : rules.size();
        if (rules != null && deviceSmvMap != null) {
            for (RuleDto rule : rules) {
                String target = rule != null && rule.getCommand() != null
                        ? rule.getCommand().getDeviceName() : null;
                DeviceSmvData targetSmv = target != null ? deviceSmvMap.get(target) : null;
                if (targetSmv != null && targetSmv.getVarName() != null
                        && !targetSmv.getVarName().isBlank()) {
                    // A compromised target deterministically drops matching rule commands.
                    String canonicalTarget = targetSmv.getVarName().trim();
                    commandTargetDevices.add(canonicalTarget);
                    effectfulDevices.add(canonicalTarget);
                    putLabel(deviceLabels, canonicalTarget, targetSmv.getDeviceLabel());
                }
            }
        }

        if (rules != null) {
            for (RuleDto rule : rules) {
                if (rule != null && rule.getId() != null && rule.getId() > 0) {
                    putLabel(linkLabels, rule.getId(), rule.getRuleString());
                }
            }
        }

        return new AttackSurface(effectfulDevices, linkCount,
                falsifiableReadingDevices, commandTargetDevices, deviceLabels, linkLabels);
    }

    private static <K> void putLabel(Map<K, String> labels, K key, String value) {
        if (key != null && value != null && !value.isBlank()) {
            labels.putIfAbsent(key, value.trim());
        }
    }

    private static Set<String> firstDevices(Set<String> deviceVarNames, int count) {
        if (deviceVarNames == null || count <= 0) {
            return Set.of();
        }
        Set<String> result = new LinkedHashSet<>();
        for (String deviceVarName : deviceVarNames) {
            if (result.size() >= count) {
                break;
            }
            result.add(deviceVarName);
        }
        return result;
    }
}
