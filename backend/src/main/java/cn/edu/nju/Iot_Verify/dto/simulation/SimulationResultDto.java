package cn.edu.nju.Iot_Verify.dto.simulation;

import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelPlaybackSceneDto;
import cn.edu.nju.Iot_Verify.dto.model.RunPersistenceDto;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonProperty;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * 模拟结果 DTO
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class SimulationResultDto {

    /** Whether this trajectory included compromised device-instance and automation-link behavior. */
    @JsonProperty("isAttack")
    private Boolean isAttack;

    /** Maximum compromised device-instance or automation-link points in the trajectory model. */
    private int attackBudget;

    /** Whether private-data propagation variables were included in the model. */
    private boolean enablePrivacy;

    /** Structured assumptions needed to interpret this trajectory. */
    private ModelSemanticsDto modelSemantics;

    /** Immutable submitted-model scope from which this one possible trajectory was generated. */
    private ModelRunSnapshotDto modelSnapshot;

    /** Exact device layout and rules shown while replaying this trajectory. */
    private ModelPlaybackSceneDto playbackScene;

    /** NOT_REQUESTED for preview-only simulation; saved-trace responses use SimulationTraceDto. */
    private RunPersistenceDto historyPersistence;

    /** Whether every submitted automation rule was present in the generated model. */
    private boolean modelComplete;

    /** Number of submitted rules disabled fail-closed during model generation. */
    private int disabledRuleCount;

    /** Per-rule explanations for any automation omitted from the generated model. */
    private List<ModelGenerationIssueDto> generationIssues;

    /** 模拟轨迹状态列表（初始状态 + N 步） */
    private List<TraceStateDto> states;

    /** 实际模拟步数（states.size() - 1，不含初始状态） */
    private int steps;

    /** 用户请求的模拟步数 */
    private int requestedSteps;

    /** NuSMV 原始输出（截断） */
    private String nusmvOutput;

    /** 执行日志 */
    private List<String> logs;

    /**
     * The exact model that was run, carried from generation to persistence.
     *
     * <p>The generator writes it into a randomly-named temp directory that is deleted after the run,
     * so the only place it can be read is where the file handle still exists. Every caller that
     * persists a trajectory takes it from here; it is never serialized to a client, which fetches
     * the model through {@code GET /api/simulate/traces/{id}/smv} instead.
     */
    @JsonIgnore
    private String smvModelContent;

    /**
     * Whether a model was captured for this run, so a client can offer the download straight after a
     * synchronous run instead of waiting to reload the trajectory from history.
     *
     * <p>This was missing while the UI already gated its download button on {@code hasSmvModel}: the
     * field was simply absent from the response, so the button never rendered and the feature was
     * unreachable from the simulation result dialog. Mirrors
     * {@code VerificationResultDto#hasSmvModel}.
     */
    @JsonProperty("hasSmvModel")
    public boolean hasSmvModel() {
        return smvModelContent != null && !smvModelContent.isBlank();
    }
}
