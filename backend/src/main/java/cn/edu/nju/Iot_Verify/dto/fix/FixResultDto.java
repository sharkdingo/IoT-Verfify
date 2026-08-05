package cn.edu.nju.Iot_Verify.dto.fix;

import cn.edu.nju.Iot_Verify.dto.model.ModelGenerationIssueDto;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FixResultDto {
    private Long traceId;
    private String violatedSpecId;
    @Builder.Default
    private List<FaultRuleDto> faultRules = List.of();
    @Builder.Default
    private List<FixSuggestionDto> suggestions = List.of();
    @Builder.Default
    private List<FixStrategyAttemptDto> strategyAttempts = List.of();
    private boolean fixable;
    /*
     * Primitives, matching `FaultLocalizationResultDto`, because the contract already forbids null here.
     *
     * These three describe whether the model this fix was verified against covered the whole board — the same
     * question `modelComplete` answers for a verdict — and the frontend's `validateSourceModel` *requires* all
     * three, cross-checking the counts against `sourceGenerationIssues`. So a null was never acceptable on the
     * wire; the boxed types merely permitted one the boundary would reject.
     *
     * `FixServiceImpl.applySourceModelMetadata` sets all three unconditionally on the single return path (the AI
     * tool goes through the same `fixService.fix`), and each source getter defaults rather than returning null —
     * so this was a latent type-level asymmetry with its twin DTO, not a live defect. Making the types say what
     * the code already guarantees means a future builder cannot omit them silently.
     */
    private boolean sourceModelComplete;
    private int sourceDisabledRuleCount;
    private int sourceSkippedSpecCount;
    @Builder.Default
    private List<ModelGenerationIssueDto> sourceGenerationIssues = List.of();
    @Builder.Default
    private TemplateSnapshotComparison templateSnapshotComparison = TemplateSnapshotComparison.NOT_CHECKED;
    private String summary;
    /** Non-fatal limitations that affect how the result should be interpreted. */
    @Builder.Default
    private List<String> warnings = List.of();
    /** Numeric conditions eligible for trace-scoped preferred-range selection. */
    @Builder.Default
    private List<ParameterTarget> parameterTargets = List.of();
    /** Preferred range selections that did not match any parameterizable condition (informational). */
    @Builder.Default
    private List<PreferredRangeSelection> unusedPreferredRangeSelections = List.of();
}
