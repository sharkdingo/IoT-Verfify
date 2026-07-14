package cn.edu.nju.Iot_Verify.dto.board;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class EnvironmentVariableChangeDto {

    public enum ChangeType {
        ADDED,
        UPDATED,
        REMOVED
    }

    private ChangeType changeType;
    private String name;
    private BoardEnvironmentVariableDto previousValue;
    private BoardEnvironmentVariableDto currentValue;
}
