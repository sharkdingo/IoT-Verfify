package cn.edu.nju.Iot_Verify.exception;

/** An upstream AI/provider response could not be used as the requested product result. */
public class BadGatewayException extends BaseException {

    public BadGatewayException(String message) {
        super(502, message);
    }

    public BadGatewayException(String message, Throwable cause) {
        super(502, message, cause);
    }
}
