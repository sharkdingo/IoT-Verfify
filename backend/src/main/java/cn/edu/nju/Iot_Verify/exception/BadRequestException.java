package cn.edu.nju.Iot_Verify.exception;

public class BadRequestException extends BaseException {

    public BadRequestException(String message) {
        super(400, message);
    }

    public BadRequestException(String message, Throwable cause) {
        super(400, message, cause);
    }
}
