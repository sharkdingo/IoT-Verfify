package cn.edu.nju.Iot_Verify.component.fuzz;

import cn.edu.nju.Iot_Verify.component.fuzz.paper.PaperEventDomainSnapshot;
import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzPaperDeviceDomainDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzPaperDomainPreviewDto;
import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzPaperEnvironmentDomainDto;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import org.springframework.stereotype.Component;

import java.util.LinkedHashMap;
import java.util.Map;

/** Builds the public paper input-domain preview from the same executable model used by a run. */
@Component
public final class FuzzPaperDomainPreviewer {

    public FuzzPaperDomainPreviewDto preview(
            ModelInputSnapshot snapshot,
            int pathLength,
            String modelFingerprint) {
        FuzzModel model = FuzzModel.from(snapshot);
        PaperEventDomainSnapshot domain = model.paperEventDomain(pathLength);
        Map<String, String> labelsByTarget = deviceLabels(snapshot);
        return FuzzPaperDomainPreviewDto.builder()
                .pathLength(domain.traceLength())
                .initializationPolicy(FuzzPaperSemantics.INITIALIZATION_POLICY)
                .modelFingerprint(modelFingerprint)
                .paperSemanticsCodes(FuzzPaperSemantics.limitationCodes())
                .deviceDomains(domain.deviceDomains().stream()
                        .map(device -> FuzzPaperDeviceDomainDto.builder()
                                .targetId(device.targetId())
                                .label(labelsByTarget.getOrDefault(
                                        device.targetId(), device.targetId()))
                                .property(device.property())
                                .legalValues(device.legalValues())
                                .build())
                        .toList())
                .localVariableDomains(domain.localVariableDomains().stream()
                        .map(variable -> FuzzPaperDeviceDomainDto.builder()
                                .targetId(variable.targetId())
                                .label(labelsByTarget.getOrDefault(
                                        variable.targetId(), variable.targetId()))
                                .property(variable.property())
                                .legalValues(variable.legalValues())
                                .lowerBound(variable.lowerBound())
                                .upperBound(variable.upperBound())
                                .build())
                        .toList())
                .environmentDomains(domain.environmentDomains().stream()
                        .map(environment -> FuzzPaperEnvironmentDomainDto.builder()
                                .name(environment.name())
                                .targetId(environment.targetId())
                                .property(environment.property())
                                .eventValueKind(environment.hasRateDomain()
                                        ? FuzzPaperSemantics.CHANGE_RATE
                                        : FuzzPaperSemantics.DIRECT_VALUE_EXTENSION)
                                .initialLowerBound(environment.valueLowerBound())
                                .initialUpperBound(environment.valueUpperBound())
                                .eventRateLowerBound(environment.rateLowerBound())
                                .eventRateUpperBound(environment.rateUpperBound())
                                .initialValues(environment.initialStateValues())
                                .eventValues(environment.eventValues())
                                .build())
                        .toList())
                .build();
    }

    private Map<String, String> deviceLabels(ModelInputSnapshot snapshot) {
        Map<String, String> labels = new LinkedHashMap<>();
        if (snapshot == null) return labels;
        for (DeviceVerificationDto device : snapshot.devices()) {
            if (device == null || device.getVarName() == null || device.getVarName().isBlank()) {
                continue;
            }
            String targetId = device.getVarName().trim();
            String label = device.getDeviceLabel();
            labels.putIfAbsent(targetId,
                    label == null || label.isBlank() ? targetId : label.trim());
        }
        return labels;
    }
}
