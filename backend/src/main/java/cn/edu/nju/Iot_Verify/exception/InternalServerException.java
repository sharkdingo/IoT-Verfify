package cn.edu.nju.Iot_Verify.exception;

public class InternalServerException extends BaseException {

    public InternalServerException(String message) {
        super(500, message);
    }

    public InternalServerException(String message, Throwable cause) {
        super(500, message, cause);
    }

    public static InternalServerException jsonSerializationFailed(Throwable cause) {
        return new InternalServerException("Failed to serialize data", cause);
    }

    public static InternalServerException jsonDeserializationFailed(Throwable cause) {
        return new InternalServerException("Failed to deserialize data", cause);
    }

    public static InternalServerException databaseError(Throwable cause) {
        return new InternalServerException("Database operation failed", cause);
    }

    public static InternalServerException aiServiceError(Throwable cause) {
        return new InternalServerException("AI service error", cause);
    }
}
