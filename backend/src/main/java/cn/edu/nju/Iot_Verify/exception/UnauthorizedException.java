package cn.edu.nju.Iot_Verify.exception;

public class UnauthorizedException extends BaseException {

    public UnauthorizedException(String message) {
        super(401, message);
    }

    public UnauthorizedException(String message, Throwable cause) {
        super(401, message, cause);
    }

    public static UnauthorizedException invalidToken() {
        return new UnauthorizedException("Invalid or expired token");
    }

    public static UnauthorizedException missingToken() {
        return new UnauthorizedException("Missing Authorization header");
    }

    public static UnauthorizedException expiredToken() {
        return new UnauthorizedException("Token has expired");
    }

    public static UnauthorizedException invalidCredentials() {
        return new UnauthorizedException("Phone number or password is incorrect");
    }
}
