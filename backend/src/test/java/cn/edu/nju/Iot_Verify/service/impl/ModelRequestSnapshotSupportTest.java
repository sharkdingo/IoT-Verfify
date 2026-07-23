package cn.edu.nju.Iot_Verify.service.impl;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelTokenSource;
import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

class ModelRequestSnapshotSupportTest {

    @Test
    void preservesExactServerOwnedTokenProvenance() {
        DeviceVerificationDto source = device(ModelTokenSource.BUNDLED);
        DeviceVerificationDto snapshot = device(ModelTokenSource.UNKNOWN);

        ModelRequestSnapshotSupport.preserveDeviceMetadata(
                List.of(source), List.of(snapshot));

        assertEquals(ModelTokenSource.BUNDLED, snapshot.getModelTokenSource());
    }

    @Test
    void rejectsSnapshotShapeAndProvenanceDrift() {
        DeviceVerificationDto source = device(ModelTokenSource.CUSTOM);
        assertThrows(IllegalArgumentException.class,
                () -> ModelRequestSnapshotSupport.preserveDeviceMetadata(
                        List.of(source), List.of()));

        source.setModelTokenSource(null);
        assertThrows(IllegalArgumentException.class,
                () -> ModelRequestSnapshotSupport.preserveDeviceMetadata(
                        List.of(source), List.of(device(ModelTokenSource.UNKNOWN))));

        assertThrows(IllegalArgumentException.class,
                () -> ModelRequestSnapshotSupport.preserveDeviceMetadata(null, List.of()));
    }

    @Test
    void preservesEquivalentMissingListsForRequestValidation() {
        assertDoesNotThrow(() -> ModelRequestSnapshotSupport.preserveDeviceMetadata(null, null));
    }

    private DeviceVerificationDto device(ModelTokenSource source) {
        DeviceVerificationDto device = new DeviceVerificationDto();
        device.setVarName("device-1");
        device.setTemplateName("Switch");
        device.setModelTokenSource(source);
        return device;
    }
}
