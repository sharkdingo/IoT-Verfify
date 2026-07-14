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
public class FaultLocalizationResultDto {
    private Long traceId;
    private String violatedSpecId;
    private boolean sourceModelComplete;
    private int sourceDisabledRuleCount;
    private int sourceSkippedSpecCount;
    @Builder.Default
    private List<ModelGenerationIssueDto> sourceGenerationIssues = List.of();
    @Builder.Default
    private List<FaultRuleDto> faultRules = List.of();
    private String summary;
    @Builder.Default
    private List<String> warnings = List.of();
}
