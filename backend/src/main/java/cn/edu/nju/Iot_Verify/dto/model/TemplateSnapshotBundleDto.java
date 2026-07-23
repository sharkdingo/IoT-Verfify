package cn.edu.nju.Iot_Verify.dto.model;

import cn.edu.nju.Iot_Verify.dto.device.DeviceTemplateDto.DeviceManifest;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.LinkedHashMap;
import java.util.Map;

/** Internal persisted envelope for one verification run's frozen template inputs. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class TemplateSnapshotBundleDto {

    public static final int CURRENT_SCHEMA_VERSION = 1;

    @Builder.Default
    private int schemaVersion = CURRENT_SCHEMA_VERSION;

    @Builder.Default
    private Map<String, DeviceManifest> manifests = Map.of();

    /** Canonical device varName -> server-captured model-token provenance. */
    @Builder.Default
    private Map<String, ModelTokenSource> modelTokenSourcesByDeviceId = Map.of();

    public static TemplateSnapshotBundleDto captured(
            Map<String, DeviceManifest> manifests,
            Map<String, ModelTokenSource> modelTokenSourcesByDeviceId) {
        return TemplateSnapshotBundleDto.builder()
                .manifests(copy(manifests))
                .modelTokenSourcesByDeviceId(copy(modelTokenSourcesByDeviceId))
                .build();
    }

    private static <K, V> Map<K, V> copy(Map<K, V> values) {
        return values == null || values.isEmpty() ? Map.of() : new LinkedHashMap<>(values);
    }
}
