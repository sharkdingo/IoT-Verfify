package cn.edu.nju.Iot_Verify.dto.trace;

import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelPlaybackSceneDto;
import com.fasterxml.jackson.annotation.JsonIgnore;
import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;
import jakarta.validation.Valid;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;
import java.util.List;

/**
 * 验证轨迹传输对象
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class TraceDto {
    /**
     * 数据库ID
     */
    private Long id;
    
    /**
     * 用户ID
     */
    @JsonIgnore
    @NotNull(message = "User ID is required")
    private Long userId;
    
    /** Owning completed verification-run id; absent only before a result is persisted. */
    private Long verificationTaskId;
    
    /**
     * 违反的规格ID
     */
    private String violatedSpecId;
    
    /**
     * Internal persisted specification snapshot. API clients receive the parsed
     * {@link #violatedSpec} object instead of having to parse an implementation JSON string.
     */
    @JsonIgnore
    private String violatedSpecJson;

    /** Structured verification-time specification snapshot for user-facing trace context. */
    private SpecificationDto violatedSpec;

    /** Exact CTL/LTL expression emitted to NuSMV for the violated specification. */
    private String checkedExpression;
    
    /**
     * 状态序列
     */
    @Valid
    @NotNull(message = "States are required")
    private List<TraceStateDto> states;

    /**
     * 验证请求快照（设备、规则、规约、参数），用于修复功能恢复上下文。
     * 不序列化到 API 响应，仅供内部 FixService 使用。
     */
    @JsonIgnore
    private String requestJson;

    /** Exact manifests used by this run, retained only for server-side replay and drift checks. */
    @JsonIgnore
    private String templateSnapshotsJson;

    /** Generation omissions from the verification run that produced this trace. */
    private Integer disabledRuleCount;

    private Integer skippedSpecCount;

    private Boolean modelComplete;

    private List<ModelGenerationIssueDto> generationIssues;

    /**
     * 验证时的攻击模式开关，与轨迹的模型语义一起持久化。
     * 暴露给前端，使历史 trace 能显示自身的验证上下文，而非当前表单。
     */
    @JsonProperty("isAttack")
    private Boolean attack;

    /**
     * 验证时的攻击预算，与轨迹的模型语义一起持久化。
     */
    private Integer attackBudget;

    /**
     * 验证时的隐私维度开关，与轨迹的模型语义一起持久化。
     */
    private Boolean enablePrivacy;

    /** Structured semantics derived from the stored run context. */
    private ModelSemanticsDto modelSemantics;

    private ModelRunSnapshotDto modelSnapshot;

    /** Exact device layout and rules shown while replaying this historical evidence. */
    private ModelPlaybackSceneDto playbackScene;

    /** Model source for the download endpoint; too large for the ordinary trace response. */
    @JsonIgnore
    private String smvModelContent;

    /**
     * Whether this trace has a stored model, so the client can offer the download only when it can
     * succeed.
     *
     * <p>The content itself stays out of the response, which left the client with no way to tell a
     * trace that carries a model from one that does not — so it gated the download button on the
     * trace id instead, showed it for every trace, and any trace written before the model was
     * persisted produced a failed download with no way for the user to know why.
     */
    @JsonProperty("hasSmvModel")
    public boolean hasSmvModel() {
        return smvModelContent != null && !smvModelContent.isBlank();
    }

    /**
     * 创建时间
     */
    private LocalDateTime createdAt;
}
