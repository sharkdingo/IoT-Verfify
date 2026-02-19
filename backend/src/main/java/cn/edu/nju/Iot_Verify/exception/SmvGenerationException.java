package cn.edu.nju.Iot_Verify.exception;

/**
 * Exception thrown when SMV model generation fails.
 */
public class SmvGenerationException extends InternalServerException {

    private final String errorCategory;

    private SmvGenerationException(String message, String errorCategory) {
        super(message);
        this.errorCategory = errorCategory;
    }

    private SmvGenerationException(String message, String errorCategory, Throwable cause) {
        super(message, cause);
        this.errorCategory = errorCategory;
    }

    public String getErrorCategory() {
        return errorCategory;
    }

    // ==================== Static Factory Methods ====================

    public static SmvGenerationException templateNotFound(String deviceId, String templateName) {
        return new SmvGenerationException(
                "Template not found for device [" + deviceId + "]: " + templateName,
                "TEMPLATE_NOT_FOUND"
        );
    }

    public static SmvGenerationException templateInvalid(String deviceId, String reason) {
        return new SmvGenerationException(
                "Invalid template for device [" + deviceId + "]: " + reason,
                "TEMPLATE_INVALID"
        );
    }

    public static SmvGenerationException manifestParseError(String templateName, Throwable cause) {
        return new SmvGenerationException(
                "Failed to parse manifest for template [" + templateName + "]: " + cause.getMessage(),
                "MANIFEST_PARSE_ERROR",
                cause
        );
    }

    public static SmvGenerationException deviceNotFound(String deviceId) {
        return new SmvGenerationException(
                "Device not found in SMV map: " + deviceId,
                "DEVICE_NOT_FOUND"
        );
    }

    public static SmvGenerationException ruleProcessingError(String ruleId, String reason) {
        return new SmvGenerationException(
                "Failed to process rule [" + ruleId + "]: " + reason,
                "RULE_PROCESSING_ERROR"
        );
    }

    public static SmvGenerationException specificationError(String specId, String reason) {
        return new SmvGenerationException(
                "Invalid specification [" + specId + "]: " + reason,
                "SPECIFICATION_ERROR"
        );
    }

    public static SmvGenerationException transitionError(String deviceId, String reason) {
        return new SmvGenerationException(
                "Failed to build transition for device [" + deviceId + "]: " + reason,
                "TRANSITION_ERROR"
        );
    }

    public static SmvGenerationException smvGenerationError(String reason) {
        return new SmvGenerationException(
                "SMV generation failed: " + reason,
                "SMV_GENERATION_ERROR"
        );
    }

    public static SmvGenerationException multipleDevicesFailed(String failedDevices) {
        return new SmvGenerationException(
                "Cannot generate SMV model: templates not found for " + failedDevices,
                "MULTIPLE_DEVICES_FAILED"
        );
    }

    // ==================== 模型校验 (P1-P5) ====================

    public static SmvGenerationException illegalTriggerAttribute(String device, String transitionOrApi, String attr, Object legalAttrs) {
        return new SmvGenerationException(
                String.format("Device '%s': '%s' has illegal trigger attribute '%s'. Legal attributes: %s",
                        device, transitionOrApi, attr, legalAttrs),
                "ILLEGAL_TRIGGER_ATTRIBUTE"
        );
    }

    public static SmvGenerationException invalidStateFormat(String device, String itemType, String itemName,
                                                            String stateStr, String reason) {
        return new SmvGenerationException(
                String.format("Device '%s': %s '%s' has invalid StartState/EndState '%s': %s",
                        device, itemType, itemName, stateStr, reason),
                "INVALID_STATE_FORMAT"
        );
    }

    public static SmvGenerationException envVarConflict(String varName, String reason) {
        return new SmvGenerationException(
                String.format("Env variable '%s' conflict: %s", varName, reason),
                "ENV_VAR_CONFLICT"
        );
    }

    public static SmvGenerationException trustPrivacyConflict(String device, String key, String prev, String current) {
        return new SmvGenerationException(
                String.format("Device '%s': trust/privacy conflict for '%s': '%s' vs '%s'",
                        device, key, prev, current),
                "TRUST_PRIVACY_CONFLICT"
        );
    }

    // ==================== Error Categories ====================

    public static class ErrorCategories {
        public static final String TEMPLATE_NOT_FOUND = "TEMPLATE_NOT_FOUND";
        public static final String TEMPLATE_INVALID = "TEMPLATE_INVALID";
        public static final String MANIFEST_PARSE_ERROR = "MANIFEST_PARSE_ERROR";
        public static final String DEVICE_NOT_FOUND = "DEVICE_NOT_FOUND";
        public static final String RULE_PROCESSING_ERROR = "RULE_PROCESSING_ERROR";
        public static final String SPECIFICATION_ERROR = "SPECIFICATION_ERROR";
        public static final String TRANSITION_ERROR = "TRANSITION_ERROR";
        public static final String SMV_GENERATION_ERROR = "SMV_GENERATION_ERROR";
        public static final String MULTIPLE_DEVICES_FAILED = "MULTIPLE_DEVICES_FAILED";
        public static final String ILLEGAL_TRIGGER_ATTRIBUTE = "ILLEGAL_TRIGGER_ATTRIBUTE";
        public static final String INVALID_STATE_FORMAT = "INVALID_STATE_FORMAT";
        public static final String ENV_VAR_CONFLICT = "ENV_VAR_CONFLICT";
        public static final String TRUST_PRIVACY_CONFLICT = "TRUST_PRIVACY_CONFLICT";
    }
}
