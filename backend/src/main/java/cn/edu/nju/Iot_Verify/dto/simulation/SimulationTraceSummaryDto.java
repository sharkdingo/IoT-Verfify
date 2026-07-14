package cn.edu.nju.Iot_Verify.dto.simulation;

import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;

import com.fasterxml.jackson.annotation.JsonProperty;
import com.fasterxml.jackson.annotation.JsonInclude;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;
import java.util.List;

/**
 * 模拟轨迹摘要 DTO（列表接口用，不含大 JSON 字段）
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class SimulationTraceSummaryDto {

    private Long id;

    private int requestedSteps;

    private int steps;

    private boolean modelComplete;

    private int disabledRuleCount;

    private List<ModelGenerationIssueDto> generationIssues;

    @JsonProperty("isAttack")
    private Boolean attack;

    private Integer attackBudget;

    private Boolean enablePrivacy;

    private ModelRunSnapshotDto modelSnapshot;

    private LocalDateTime createdAt;

    @Builder.Default
    private Boolean dataAvailable = true;

    private String unavailableReasonCode;
}
