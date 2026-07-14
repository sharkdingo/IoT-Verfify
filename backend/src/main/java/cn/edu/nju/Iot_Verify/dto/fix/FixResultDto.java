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
    private Boolean sourceModelComplete;
    private Integer sourceDisabledRuleCount;
    private Integer sourceSkippedSpecCount;
    @Builder.Default
    private List<ModelGenerationIssueDto> sourceGenerationIssues = List.of();
    @Builder.Default
    private TemplateSnapshotComparison templateSnapshotComparison = TemplateSnapshotComparison.NOT_CHECKED;
    private String summary;
    /** Non-fatal limitations that affect how the result should be interpreted. */
    @Builder.Default
    private List<String> warnings = List.of();
    /** Preferred range selections that did not match any parameterizable condition (informational). */
    @Builder.Default
    private List<PreferredRangeSelection> unusedPreferredRangeSelections = List.of();
}
