package cn.edu.nju.Iot_Verify.dto.fuzz;

import jakarta.validation.constraints.Max;
import jakarta.validation.constraints.Min;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FuzzWorkloadPreviewRequestDto {

    // Kept identical to FuzzRequestDto's default so a preview taken with no explicit budget describes the
    // same request submission would build.
    @NotNull(message = "Maximum iterations cannot be null")
    @Min(value = 1, message = "Maximum iterations must be at least 1")
    @Max(value = 5_000, message = "Maximum iterations must be at most 5000")
    @Builder.Default
    private Integer maxIterations = 200;

    @NotNull(message = "Path length cannot be null")
    @Min(value = 1, message = "Path length must be at least 1")
    @Max(value = 50, message = "Path length must be at most 50")
    @Builder.Default
    private Integer pathLength = 20;

    @NotNull(message = "Population size cannot be null")
    @Min(value = 1, message = "Population size must be at least 1")
    @Max(value = 50, message = "Population size must be at most 50")
    @Builder.Default
    private Integer populationSize = 10;

    /**
     * Which exploration mode the preview is for.
     *
     * <p>Required because model complexity is mode-dependent: {@code PAPER_COMPATIBLE} pays for the monitor's
     * predecessor walk and {@code BOARD_SNAPSHOT} does not. A preview computed for the wrong mode would
     * report an estimate the submit endpoint disagrees with — accepted here, rejected there.</p>
     */
    @NotNull(message = "Exploration mode cannot be null")
    @Builder.Default
    private FuzzExplorationMode explorationMode = FuzzExplorationMode.BOARD_SNAPSHOT;
}
