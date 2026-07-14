package cn.edu.nju.Iot_Verify.dto.verification;

import cn.edu.nju.Iot_Verify.dto.trace.TraceDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelSemanticsDto;
import cn.edu.nju.Iot_Verify.dto.model.ModelRunSnapshotDto;
import cn.edu.nju.Iot_Verify.dto.model.RunPersistenceDto;
import com.fasterxml.jackson.annotation.JsonProperty;
import lombok.Builder;
import lombok.Data;

import java.util.List;

/**
 * 验证结果
 */
@Data
@Builder
public class VerificationResultDto {
    /** Whether the generated model included compromised device-instance and automation-link behavior. */
    @JsonProperty("isAttack")
    private Boolean isAttack;

    /** Maximum compromised device-instance or automation-link points allowed in any checked branch. */
    private int attackBudget;

    /** Whether private-data propagation variables were included in the model. */
    private boolean enablePrivacy;

    /** Structured assumptions needed to interpret this result without frontend guesswork. */
    private ModelSemanticsDto modelSemantics;

    /** Immutable submitted-model scope to which this conclusion applies. */
    private ModelRunSnapshotDto modelSnapshot;

    /** Whether this synchronous result was also committed to run history. */
    private RunPersistenceDto historyPersistence;

    /**
     * Explicit user-facing conclusion. This distinguishes a property violation from
     * an incomplete or unreliable check.
     */
    private VerificationOutcome outcome;

    /**
     * Whether the checked model included every submitted rule and specification and
     * produced a reliable per-spec result set.
     */
    private boolean modelComplete;

    /**
     * 错误轨迹列表
     */
    private List<TraceDto> traces;

    /**
     * 每个规格的检查结果
     */
    private List<SpecResultDto> specResults;

    /**
     * 检查日志
     */
    private List<String> checkLogs;

    /**
     * Number of automation rules disabled during SMV generation.
     */
    private int disabledRuleCount;

    /**
     * Number of specifications omitted from NuSMV because they could not be checked.
     */
    private int skippedSpecCount;

    /** Per-item explanations for every rule/specification omitted from the generated model. */
    private List<ModelGenerationIssueDto> generationIssues;

    /**
     * 原始 NuSMV 输出
     */
    private String nusmvOutput;
}
