package cn.edu.nju.Iot_Verify.dto.fuzz;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FuzzWorkloadPreviewDto {

    private int maxIterations;
    private int pathLength;
    private int populationSize;
    /** Echoed so a client can reject a preview computed for a mode it is no longer offering. */
    private FuzzExplorationMode explorationMode;
    private long modelComplexityUnits;
    private long estimatedWorkload;
    private long workloadLimit;
    private boolean accepted;

    /**
     * Largest {@code maxIterations} this board admits at the previewed path length and population size.
     *
     * <p>The server already holds every factor, so computing this here turns a rejection into one edit
     * instead of a guess-and-check loop against a debounced round trip.</p>
     */
    private int maxAcceptedIterations;
}
