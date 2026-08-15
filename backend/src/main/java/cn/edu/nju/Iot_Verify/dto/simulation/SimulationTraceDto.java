package cn.edu.nju.Iot_Verify.dto.simulation;

import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelPlaybackSceneDto;
import cn.edu.nju.Iot_Verify.dto.model.RunPersistenceDto;
import cn.edu.nju.Iot_Verify.dto.model.RunInitiator;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;
import java.util.List;

/**
 * 模拟轨迹详情 DTO（含完整 states/logs）
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class SimulationTraceDto {

    private Long id;

    private RunInitiator initiator;

    @JsonIgnore
    private Long userId;

    private int requestedSteps;

    private int steps;

    private boolean modelComplete;

    private int disabledRuleCount;

    private List<ModelGenerationIssueDto> generationIssues;

    /** 模拟轨迹状态列表 */
    private List<TraceStateDto> states;

    /** 执行日志 */
    private List<String> logs;

    /** NuSMV 原始输出（截断） */
    private String nusmvOutput;

    /** Internal request snapshot used to derive the structured execution context below. */
    @JsonIgnore
    private String requestJson;

    /** Exact manifests used by this run; internal audit context, not a user-editable input. */
    @JsonIgnore
    private String templateSnapshotsJson;

    /** Model source for the download endpoint; too large for the ordinary detail response. */
    @JsonIgnore
    private String smvModelContent;

    /**
     * Whether this trajectory has a stored model, so the client can offer the download only when it can
     * succeed. The content itself is {@code @JsonIgnore} (tens of thousands of characters), which without
     * this flag left the client unable to tell a trajectory that carries a model from one that does not —
     * so it gated the button on the id, showed it for every record, and any trajectory saved before the
     * model was persisted produced a failed download with no explanation.
     *
     * <p>A trajectory is its own run, which is why this exists here and has no verification-trace
     * counterpart: there, one run owns many counterexamples and the flag lives on the run.
     */
    @JsonProperty("hasSmvModel")
    public boolean hasSmvModel() {
        return smvModelContent != null && !smvModelContent.isBlank();
    }

    @JsonProperty("isAttack")
    private Boolean attack;

    private Integer attackBudget;

    private Boolean enablePrivacy;

    private ModelSemanticsDto modelSemantics;

    private ModelRunSnapshotDto modelSnapshot;

    /** Exact device layout and rules shown while replaying this historical trajectory. */
    private ModelPlaybackSceneDto playbackScene;

    /** SAVED for history details, FAILED when execution succeeded but history persistence did not. */
    private RunPersistenceDto historyPersistence;

    private LocalDateTime createdAt;
}
