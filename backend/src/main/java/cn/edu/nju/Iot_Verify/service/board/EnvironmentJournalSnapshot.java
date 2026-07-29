package cn.edu.nju.Iot_Verify.service.board;

import cn.edu.nju.Iot_Verify.dto.board.BoardEnvironmentVariableDto;

import java.util.List;

/** Complete Environment Pool state on one side of a reversible direct edit. */
public record EnvironmentJournalSnapshot(List<BoardEnvironmentVariableDto> environmentVariables) {

    public EnvironmentJournalSnapshot {
        environmentVariables = environmentVariables == null
                ? List.of()
                : List.copyOf(environmentVariables);
    }
}
