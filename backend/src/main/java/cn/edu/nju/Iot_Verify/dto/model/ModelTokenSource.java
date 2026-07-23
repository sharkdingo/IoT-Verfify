package cn.edu.nju.Iot_Verify.dto.model;

/**
 * Provenance of machine-facing model tokens returned for user-visible formatting.
 * Only {@link #BUNDLED} is safe to localize with the bundled token dictionary.
 */
public enum ModelTokenSource {
    BUNDLED,
    CUSTOM,
    UNKNOWN;

    public static ModelTokenSource fromDefaultTemplate(Boolean defaultTemplate) {
        if (Boolean.TRUE.equals(defaultTemplate)) return BUNDLED;
        if (Boolean.FALSE.equals(defaultTemplate)) return CUSTOM;
        return UNKNOWN;
    }
}
