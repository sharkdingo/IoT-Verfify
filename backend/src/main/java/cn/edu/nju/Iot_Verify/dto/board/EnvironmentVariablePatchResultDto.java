package cn.edu.nju.Iot_Verify.dto.board;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/** Explains how one name-keyed Environment Pool patch was applied. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class EnvironmentVariablePatchResultDto {

    private String name;
    @Builder.Default
    private List<String> suppliedFields = List.of();
    @Builder.Default
    private List<String> changedFields = List.of();
    @Builder.Default
    private List<String> preservedFields = List.of();
    private BoardEnvironmentVariableDto previousValue;
    private BoardEnvironmentVariableDto currentValue;
}
