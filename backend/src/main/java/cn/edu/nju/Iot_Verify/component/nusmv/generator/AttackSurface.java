package cn.edu.nju.Iot_Verify.component.nusmv.generator;

import cn.edu.nju.Iot_Verify.component.nusmv.generator.data.DeviceSmvData;
import cn.edu.nju.Iot_Verify.dto.rule.RuleDto;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** The compromise choices that can actually change behavior in the generated model. */
public record AttackSurface(Set<String> deviceVarNames,
                            int automationLinkCount,
                            int falsifiableReadingDeviceCount) {

    public AttackSurface {
        deviceVarNames = Collections.unmodifiableSet(new LinkedHashSet<>(
                deviceVarNames == null ? Set.of() : deviceVarNames));
        automationLinkCount = Math.max(0, automationLinkCount);
        falsifiableReadingDeviceCount = Math.max(0,
                Math.min(falsifiableReadingDeviceCount, deviceVarNames.size()));
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

    public boolean hasFalsifiableReadingEffect() {
        return falsifiableReadingDeviceCount > 0;
    }

    public static AttackSurface analyze(List<RuleDto> rules, Map<String, DeviceSmvData> deviceSmvMap) {
        Set<String> effectfulDevices = new LinkedHashSet<>();
        Set<String> falsifiableReadingDevices = new LinkedHashSet<>();

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
                    effectfulDevices.add(targetSmv.getVarName().trim());
                }
            }
        }

        return new AttackSurface(effectfulDevices, linkCount, falsifiableReadingDevices.size());
    }
}
