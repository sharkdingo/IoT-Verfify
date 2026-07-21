package cn.edu.nju.Iot_Verify.exception;

import lombok.Getter;

@Getter
public class AuthRateLimitException extends BaseException {

    private final String reasonCode;
    private final String scope;
    private final long retryAfterSeconds;

    public AuthRateLimitException(String operation, String scope, long retryAfterSeconds) {
        super(429, "Too many " + operation + " attempts; retry later");
        this.reasonCode = "AUTH_" + operation.toUpperCase() + "_RATE_LIMIT_REACHED";
        this.scope = scope;
        this.retryAfterSeconds = Math.max(1, retryAfterSeconds);
    }
}
