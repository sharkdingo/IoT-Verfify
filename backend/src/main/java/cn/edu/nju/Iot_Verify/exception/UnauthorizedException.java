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

    /*
     * No `expiredToken()`: its only caller was `JwtUtil.validateTokenOrThrow`, which had no callers of its own.
     * Expiry now reaches the client through the boolean `validateToken` path, which the filter turns into the
     * same 401 — this factory's message was never the one a user saw.
     */

    public static UnauthorizedException invalidCredentials() {
        return new UnauthorizedException("Account or password is incorrect");
    }
}
