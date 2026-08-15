package cn.edu.nju.Iot_Verify.dto.simulation;

import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.RunInitiator;

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

    private RunInitiator initiator;

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

    /**
     * Whether this trajectory still holds the SMV model it ran, gating
     * {@code GET /api/simulate/traces/{id}/smv}. Presence only — the model is tens of thousands of
     * characters and this is a list response.
     *
     * <p>A simulation trajectory *is* its own run, so unlike verification there is no separate run-keyed
     * endpoint: this trace id is the run id, and {@code historyPersistence.runId} equals it.
     *
     * <p>Boxed rather than primitive because this DTO has an unavailable arm: when persisted data fails
     * integrity checks the row becomes a placeholder with {@code dataAvailable=false}, and nothing about
     * its model can be asserted — which is a different claim from "no model". {@code JsonInclude(NON_NULL)}
     * then omits the field, and the client guard reads {@code dataAvailable && hasSmvModel} so the absent
     * value is never consulted. A primitive would make a damaged row report "no model" as fact.
     */
    private Boolean hasSmvModel;

    @Builder.Default
    private Boolean dataAvailable = true;

    private String unavailableReasonCode;
}
