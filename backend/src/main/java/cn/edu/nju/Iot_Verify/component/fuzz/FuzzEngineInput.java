package cn.edu.nju.Iot_Verify.component.fuzz;

import cn.edu.nju.Iot_Verify.util.mapper.BoardDataConverter;

/** Immutable inputs captured before a fuzzing run starts. */
public record FuzzEngineInput(
        BoardDataConverter.ModelInputSnapshot snapshot,
        FuzzEngineConfig config) {
}
