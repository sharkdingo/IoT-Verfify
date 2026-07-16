package cn.edu.nju.Iot_Verify.dto.fuzz;

import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import com.fasterxml.jackson.annotation.JsonInclude;
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
@JsonInclude(JsonInclude.Include.NON_NULL)
public class FuzzRunSummaryDto {
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
    private List<FuzzFindingSummaryDto> findings = new ArrayList<>();
    @Builder.Default
    private boolean dataAvailable = true;
    private String unavailableReasonCode;
}
