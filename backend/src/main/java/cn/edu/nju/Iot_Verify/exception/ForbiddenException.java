package cn.edu.nju.Iot_Verify.exception;

public class ForbiddenException extends BaseException {

    public ForbiddenException(String message) {
        super(403, message);
    }

    public ForbiddenException(String message, Throwable cause) {
        super(403, message, cause);
    }

}
