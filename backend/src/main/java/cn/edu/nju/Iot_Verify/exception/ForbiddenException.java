package cn.edu.nju.Iot_Verify.exception;

public class ForbiddenException extends BaseException {

    public ForbiddenException(String message) {
        super(403, message);
    }

    public ForbiddenException(String message, Throwable cause) {
        super(403, message, cause);
    }

    public static ForbiddenException accessDenied() {
        return new ForbiddenException("Access denied");
    }

    public static ForbiddenException resourceNotOwned() {
        return new ForbiddenException("You do not have permission to access this resource");
    }
}
