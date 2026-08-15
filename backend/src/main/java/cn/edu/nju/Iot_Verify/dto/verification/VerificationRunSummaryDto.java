package cn.edu.nju.Iot_Verify.dto.verification;

import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.RunInitiator;
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
    private RunInitiator initiator;
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

    /**
     * Whether this run still holds the SMV model it checked, gating
     * {@code GET /api/verify/runs/{id}/smv}. Presence only, as on {@code VerificationRunDto} — the
     * model is tens of thousands of characters and this is a list response.
     *
     * <p>Keyed on the run because all of its counterexamples share one model, and a run where every
     * specification holds has no counterexample to key on at all. This is the flag behind the history
     * panel's single per-run download.
     *
     * <p>Boxed rather than primitive because this DTO has an unavailable arm: when persisted data fails
     * integrity checks the row becomes a placeholder with {@code dataAvailable=false}, and nothing about
     * its model can be asserted — which is a different claim from "no model". {@code JsonInclude(NON_NULL)}
     * then omits the field, and the client reads it only on the available arm. A primitive would make a
     * damaged row report "no model" as fact.
     */
    private Boolean hasSmvModel;

    @Builder.Default
    private List<TraceSummaryDto> counterexamples = List.of();
    @Builder.Default
    private Boolean dataAvailable = true;
    private String unavailableReasonCode;
}
