package cn.edu.nju.Iot_Verify.dto.fix;

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
    private List<FaultRuleDto> faultRules;
    private List<FixSuggestionDto> suggestions;
    private boolean fixable;
    private String summary;
    /** Keys from preferredRanges that did not match any parameterizable condition (informational). */
    private List<String> unusedPreferredRangeKeys;
}
