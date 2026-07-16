package cn.edu.nju.Iot_Verify.component.fuzz;

import cn.edu.nju.Iot_Verify.dto.fuzz.FuzzExplorationMode;

import java.util.List;

/** Deterministic search budget and target selection. */
public record FuzzEngineConfig(
        List<String> targetSpecIds,
        int maxIterations,
        int pathLength,
        int populationSize,
        Long seed,
        FuzzExplorationMode explorationMode) {

    public FuzzEngineConfig {
        targetSpecIds = targetSpecIds == null ? List.of() : List.copyOf(targetSpecIds);
        explorationMode = explorationMode == null
                ? FuzzExplorationMode.BOARD_SNAPSHOT
                : explorationMode;
    }

    public FuzzEngineConfig(
            List<String> targetSpecIds,
            int maxIterations,
            int pathLength,
            int populationSize,
            Long seed) {
        this(targetSpecIds, maxIterations, pathLength, populationSize, seed,
                FuzzExplorationMode.BOARD_SNAPSHOT);
    }
}
