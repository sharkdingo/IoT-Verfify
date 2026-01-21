package cn.edu.nju.Iot_Verify.exception;

import lombok.Getter;

@Getter
public abstract class BaseException extends RuntimeException {

    private final int code;

    protected BaseException(int code, String message) {
        super(message);
        this.code = code;
    }

    protected BaseException(int code, String message, Throwable cause) {
        super(message, cause);
        this.code = code;
    }
}
