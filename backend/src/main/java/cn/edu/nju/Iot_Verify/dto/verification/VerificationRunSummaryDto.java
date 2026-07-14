package cn.edu.nju.Iot_Verify.dto.verification;

import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceSummaryDto;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;
import java.util.List;

/** Lightweight, completed verification-run result for history UIs. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class VerificationRunSummaryDto {

    private Long id;
    private LocalDateTime createdAt;
    private LocalDateTime startedAt;
    private LocalDateTime completedAt;
    private Long processingTimeMs;

    @JsonProperty("isAttack")
    private Boolean isAttack;

    private Integer attackBudget;
    private Boolean enablePrivacy;
    private ModelSemanticsDto modelSemantics;
    private ModelRunSnapshotDto modelSnapshot;
    private VerificationOutcome outcome;
    private Boolean modelComplete;
    private Integer violatedSpecCount;
    private Integer counterexampleCount;
    private Integer disabledRuleCount;
    private Integer skippedSpecCount;
    private List<ModelGenerationIssueDto> generationIssues;
    @Builder.Default
    private List<TraceSummaryDto> counterexamples = List.of();
    @Builder.Default
    private Boolean dataAvailable = true;
    private String unavailableReasonCode;
}
