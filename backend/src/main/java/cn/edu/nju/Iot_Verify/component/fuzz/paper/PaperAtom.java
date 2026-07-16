package cn.edu.nju.Iot_Verify.component.fuzz.paper;

import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;

import java.util.Objects;

/** Immutable identity of one structured specification condition. */
public record PaperAtom(
        String deviceId,
        String targetType,
        String key,
        String propertyScope,
        String relation,
        String value) {

    public PaperAtom {
        deviceId = required(deviceId, "deviceId");
        targetType = required(targetType, "targetType");
        key = required(key, "key");
        relation = required(relation, "relation");
        value = required(value, "value");
        propertyScope = propertyScope == null || propertyScope.isBlank() ? null : propertyScope.trim();
    }

    public static PaperAtom from(SpecConditionDto condition) {
        Objects.requireNonNull(condition, "condition");
        return new PaperAtom(
                condition.getDeviceId(),
                condition.getTargetType(),
                condition.getKey(),
                condition.getPropertyScope(),
                condition.getRelation(),
                condition.getValue());
    }

    private static String required(String value, String field) {
        if (value == null || value.isBlank()) {
            throw new IllegalArgumentException(field + " is required");
        }
        return value.trim();
    }
}
