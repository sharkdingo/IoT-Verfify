package cn.edu.nju.Iot_Verify.dto.board;

import cn.edu.nju.Iot_Verify.dto.model.ModelTokenSource;
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
    @Builder.Default
    private ModelTokenSource previousModelTokenSource = ModelTokenSource.UNKNOWN;
    @Builder.Default
    private ModelTokenSource currentModelTokenSource = ModelTokenSource.UNKNOWN;
}
