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
        if (source == null || snapshot == null || source.size() != snapshot.size()) return;
        for (int index = 0; index < source.size(); index++) {
            DeviceVerificationDto original = source.get(index);
            DeviceVerificationDto copy = snapshot.get(index);
            if (original != null && copy != null) {
                copy.setModelTokenSource(original.getModelTokenSource() != null
                        ? original.getModelTokenSource()
                        : ModelTokenSource.UNKNOWN);
            }
        }
    }
}
