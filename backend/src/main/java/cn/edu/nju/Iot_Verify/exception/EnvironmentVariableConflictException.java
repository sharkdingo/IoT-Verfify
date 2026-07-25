package cn.edu.nju.Iot_Verify.exception;

import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;
import lombok.Getter;

/** An Environment Pool variable changed after the caller captured its edit baseline. */
@Getter
public class EnvironmentVariableConflictException extends ConflictException {

    public static final String REASON_CODE = "ENVIRONMENT_VARIABLE_STALE";

    private final String variableName;
    private final BoardEnvironmentVariableDto currentVariable;

    public EnvironmentVariableConflictException(
            String variableName,
            BoardEnvironmentVariableDto currentVariable) {
        super("The environment variable changed or was removed after editing began. "
                + "Review the latest value before saving again.");
        this.variableName = variableName;
        this.currentVariable = currentVariable;
    }
}
