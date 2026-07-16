package cn.edu.nju.Iot_Verify.component.fuzz.paper;

import java.util.Objects;

/** One direct value assigned to a mandatory paper initial-state target. */
public record PaperInitialValue(Type type, String targetId, String property, String value) {

    public enum Type {
        DEVICE_STATE,
        ENVIRONMENT_VALUE,
        DEVICE_VARIABLE
    }

    public PaperInitialValue {
        type = Objects.requireNonNull(type, "type must not be null");
        targetId = requireText(targetId, "targetId");
        property = requireText(property, "property");
        value = requireText(value, "value");
    }

    public Target target() {
        return new Target(type, targetId, property);
    }

    public record Target(Type type, String targetId, String property) {
        public Target {
            type = Objects.requireNonNull(type, "type must not be null");
            targetId = requireText(targetId, "targetId");
            property = requireText(property, "property");
        }
    }

    private static String requireText(String value, String field) {
        if (value == null || value.isBlank()) {
            throw new IllegalArgumentException(field + " must not be blank");
        }
        return value.trim();
    }
}
