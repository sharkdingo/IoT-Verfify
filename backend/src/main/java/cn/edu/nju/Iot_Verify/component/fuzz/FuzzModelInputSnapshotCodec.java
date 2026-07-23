package cn.edu.nju.Iot_Verify.component.fuzz;

import cn.edu.nju.Iot_Verify.dto.device.DeviceVerificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelTokenSource;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter.ModelInputSnapshot;
import com.fasterxml.jackson.databind.JsonNode;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

/** Encodes the complete, server-captured fuzz input and token provenance atomically. */
public final class FuzzModelInputSnapshotCodec {

    private static final int CURRENT_SCHEMA_VERSION = 1;
    private static final Set<String> SNAPSHOT_FIELDS = Set.of(
            "nodes", "devices", "environmentVariables", "rules",
            "specifications", "templateManifests");

    private FuzzModelInputSnapshotCodec() {
    }

    public static String encode(ModelInputSnapshot snapshot) {
        return JsonUtils.toJson(PersistedSnapshot.capture(snapshot));
    }

    public static ModelInputSnapshot decode(String json) {
        JsonNode root = JsonUtils.fromJson(json, JsonNode.class);
        if (root == null || !root.isObject() || root.size() != 3
                || !root.has("schemaVersion") || !root.has("snapshot")
                || !root.has("modelTokenSourcesByDeviceId")) {
            throw new IllegalStateException("Frozen Board snapshot schema is invalid");
        }
        JsonNode schemaVersion = root.get("schemaVersion");
        JsonNode snapshotNode = root.get("snapshot");
        JsonNode sourcesNode = root.get("modelTokenSourcesByDeviceId");
        if (!schemaVersion.isInt() || !snapshotNode.isObject() || !sourcesNode.isObject()
                || snapshotNode.size() != SNAPSHOT_FIELDS.size()
                || !SNAPSHOT_FIELDS.stream().allMatch(snapshotNode::has)
                || !snapshotNode.get("nodes").isArray()
                || !snapshotNode.get("devices").isArray()
                || !snapshotNode.get("environmentVariables").isArray()
                || !snapshotNode.get("rules").isArray()
                || !snapshotNode.get("specifications").isArray()
                || !snapshotNode.get("templateManifests").isObject()
                || sourcesNode.properties().stream().anyMatch(entry -> entry.getKey().isBlank()
                || !entry.getValue().isTextual())) {
            throw new IllegalStateException("Frozen Board snapshot schema is invalid");
        }
        PersistedSnapshot persisted = JsonUtils.fromJson(json, PersistedSnapshot.class);
        if (persisted == null || !Objects.equals(persisted.schemaVersion, CURRENT_SCHEMA_VERSION)
                || persisted.snapshot == null || persisted.modelTokenSourcesByDeviceId == null
                || persisted.modelTokenSourcesByDeviceId.values().stream().anyMatch(Objects::isNull)) {
            throw new IllegalStateException("Frozen Board snapshot schema is invalid");
        }
        return persisted.restore();
    }

    private static void requireSnapshot(ModelInputSnapshot snapshot) {
        if (snapshot == null || snapshot.devices() == null) {
            throw new IllegalStateException("Frozen Board snapshot is missing");
        }
    }

    private static String requireDeviceId(DeviceVerificationDto device) {
        if (device == null || device.getVarName() == null || device.getVarName().isBlank()) {
            throw new IllegalStateException("Frozen Board snapshot contains a device without an id");
        }
        return device.getVarName().trim();
    }

    private record PersistedSnapshot(
            Integer schemaVersion,
            ModelInputSnapshot snapshot,
            Map<String, ModelTokenSource> modelTokenSourcesByDeviceId) {

        private static PersistedSnapshot capture(ModelInputSnapshot snapshot) {
            requireSnapshot(snapshot);
            Map<String, ModelTokenSource> sources = new LinkedHashMap<>();
            for (DeviceVerificationDto device : snapshot.devices()) {
                String deviceId = requireDeviceId(device);
                ModelTokenSource source = device.getModelTokenSource();
                if (source == null) {
                    throw new IllegalStateException(
                            "Frozen Board snapshot device '" + deviceId + "' has no token provenance");
                }
                if (sources.putIfAbsent(deviceId, source) != null) {
                    throw new IllegalStateException(
                            "Frozen Board snapshot contains duplicate device id '" + deviceId + "'");
                }
            }
            return new PersistedSnapshot(CURRENT_SCHEMA_VERSION, snapshot,
                    Collections.unmodifiableMap(new LinkedHashMap<>(sources)));
        }

        private ModelInputSnapshot restore() {
            requireSnapshot(snapshot);
            Set<String> deviceIds = new LinkedHashSet<>();
            for (DeviceVerificationDto device : snapshot.devices()) {
                String deviceId = requireDeviceId(device);
                if (!deviceIds.add(deviceId)) {
                    throw new IllegalStateException(
                            "Frozen Board snapshot contains duplicate device id '" + deviceId + "'");
                }
            }
            if (!modelTokenSourcesByDeviceId.keySet().equals(deviceIds)) {
                throw new IllegalStateException(
                        "Frozen Board snapshot token provenance does not match its devices");
            }
            for (DeviceVerificationDto device : snapshot.devices()) {
                ModelTokenSource source = modelTokenSourcesByDeviceId.get(device.getVarName().trim());
                if (source == null) {
                    throw new IllegalStateException("Frozen Board snapshot token provenance is incomplete");
                }
                device.setModelTokenSource(source);
            }
            return snapshot;
        }
    }
}
