package cn.edu.nju.Iot_Verify.dto.fuzz;

import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FuzzRunDto {
    private Long id;
    private FuzzOutcome outcome;
    private FuzzExplorationMode explorationMode;
    private Long effectiveSeed;
    private Integer iterations;
    private Long generatedPaths;
    private Long elapsedMs;
    private ModelRunSnapshotDto modelSnapshot;
    private FuzzEligibilityDto eligibility;
    @Builder.Default
    private List<String> limitations = new ArrayList<>();
    private LocalDateTime createdAt;
    private LocalDateTime completedAt;
    private Integer findingCount;
    private Integer maxIterations;
    private Integer pathLength;
    private Integer populationSize;
    @Builder.Default
    private List<String> targetSpecIds = new ArrayList<>();
    @Builder.Default
    private List<FuzzFindingDto> findings = new ArrayList<>();
}
