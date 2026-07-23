package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelTokenSource;

import java.util.List;

/** Preserves server-only model metadata across Jackson request snapshots. */
final class ModelRequestSnapshotSupport {

    private ModelRequestSnapshotSupport() {
    }

    static void preserveDeviceMetadata(List<DeviceVerificationDto> source,
                                       List<DeviceVerificationDto> snapshot) {
        if (source == null && snapshot == null) {
            return;
        }
        if (source == null || snapshot == null || source.size() != snapshot.size()) {
            throw new IllegalArgumentException("Snapshot device count does not match its source");
        }
        for (int index = 0; index < source.size(); index++) {
            DeviceVerificationDto original = source.get(index);
            DeviceVerificationDto copy = snapshot.get(index);
            if (original == null || copy == null || original.getModelTokenSource() == null) {
                throw new IllegalArgumentException(
                        "Snapshot device metadata is incomplete at index " + index);
            }
            ModelTokenSource tokenSource = original.getModelTokenSource();
            copy.setModelTokenSource(tokenSource);
        }
    }
}
