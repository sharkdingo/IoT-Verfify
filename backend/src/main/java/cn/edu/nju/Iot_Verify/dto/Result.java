package cn.edu.nju.Iot_Verify.dto;

import com.fasterxml.jackson.annotation.JsonInclude;
import lombok.Data;

@Data
@JsonInclude(JsonInclude.Include.NON_NULL)
public class Result<T> {
    private Integer code;
    private String message;
    private T data;

    public static <T> Result<T> success(T data) {
        Result<T> r = new Result<>();
        r.setCode(200);
        r.setMessage("success");
        r.setData(data);
        return r;
    }

    public static <T> Result<T> success() {
        return success(null);
    }

    public static <T> Result<T> error(int code, String msg) {
        Result<T> r = new Result<>();
        r.setCode(code);
        r.setMessage(msg);
        return r;
    }

    public static <T> Result<T> error(String msg) {
        return error(500, msg);
    }

    public static <T> Result<T> badRequest(String msg) {
        return error(400, msg);
    }

    public static <T> Result<T> unauthorized(String msg) {
        return error(401, msg);
    }

    public static <T> Result<T> forbidden(String msg) {
        return error(403, msg);
    }

    public static <T> Result<T> notFound(String msg) {
        return error(404, msg);
    }

    public static <T> Result<T> conflict(String msg) {
        return error(409, msg);
    }

    public static <T> Result<T> validationError(String msg) {
        return error(422, msg);
    }

    public static <T> Result<T> serviceUnavailable(String msg) {
        return error(503, msg);
    }

    public static <T> Result<T> tooManyRequests(String msg) {
        return error(429, msg);
    }
}
