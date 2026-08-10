package cn.edu.nju.Iot_Verify.component.fuzz.paper;

import cn.edu.nju.Iot_Verify.dto.spec.SpecConditionDto;

import java.util.Objects;

/**
 * Immutable identity of one structured specification condition.
 *
 * <p>Deliberately carries no {@code variableSource}. In NuSMV generation that field chooses between two
 * distinct identifiers — the shared pool value and the reporting device's mirror — which diverge exactly
 * when a device is compromised and reports a falsified reading.
 *
 * <p>The bounded explorer has <strong>one value per shared key and no per-device mirror at all</strong>:
 * {@code FuzzModel} routes an {@code IsInside=true} declaration into that device's {@code locals} and every
 * shared declaration into a single {@code environment} entry, so no structure exists that could hold a
 * reported value diverging from the pool. It also models no compromise — there are no attack points and
 * {@code setCompromised(false)} is hard-coded — which is what makes the two questions have the same answer
 * here.
 *
 * <p>One caveat, deliberately not overstated: {@code FuzzModel} resolves an atom's key as "this device's
 * locals, else the shared pool". That is unambiguous for any key declared consistently across templates,
 * and the guards against a name being both local and impacted are per-template
 * ({@code SmvModelValidator}, {@code DeviceTemplateNuSmvValidator}) — I did not find one comparing a
 * device-local name against another device's shared declaration. In a scene that did that, the lookup
 * prefers the local value. That is a pre-existing property of the explorer's flat key space, not something
 * {@code variableSource} would fix, and it is orthogonal to compromise.
 *
 * <p>If per-device readings or compromise are ever added to the explorer, this record must carry the field
 * and that resolution becomes a defect.
 */
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
