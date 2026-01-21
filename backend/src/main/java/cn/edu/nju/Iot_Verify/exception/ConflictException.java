package cn.edu.nju.Iot_Verify.exception;

public class ConflictException extends BaseException {

    public ConflictException(String message) {
        super(409, message);
    }

    public ConflictException(String message, Throwable cause) {
        super(409, message, cause);
    }

    public static ConflictException duplicatePhone(String phone) {
        return new ConflictException("Phone number already registered: " + phone);
    }

    public static ConflictException duplicateUsername(String username) {
        return new ConflictException("Username already exists: " + username);
    }

    public static ConflictException duplicateTemplate(String name) {
        return new ConflictException("Device template already exists: " + name);
    }
}
