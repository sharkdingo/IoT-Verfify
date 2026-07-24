package cn.edu.nju.Iot_Verify.exception;

/**
 * The chat turn was durably admitted, but a required pre-dispatch rollback could not be confirmed.
 */
public class ChatAdmissionOutcomeUnknownException extends RuntimeException {
    public ChatAdmissionOutcomeUnknownException(String message, Throwable cause) {
        super(message, cause);
    }
}
