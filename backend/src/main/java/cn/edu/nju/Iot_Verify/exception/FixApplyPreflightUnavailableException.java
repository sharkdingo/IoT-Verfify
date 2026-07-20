package cn.edu.nju.Iot_Verify.exception;

/** A retryable automatic-fix apply rejection proven to occur before any board write. */
public class FixApplyPreflightUnavailableException extends ServiceUnavailableException {

    public static final String REASON_CODE = "FIX_APPLY_PREFLIGHT_UNAVAILABLE";

    public FixApplyPreflightUnavailableException(String message) {
        super(message);
    }

    public FixApplyPreflightUnavailableException(String message, Throwable cause) {
        super(message, cause);
    }
}
