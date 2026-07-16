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
    private long modelComplexityUnits;
    private long estimatedWorkload;
    private long workloadLimit;
    private boolean accepted;
}
