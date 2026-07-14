package cn.edu.nju.Iot_Verify.dto.model;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

/** Structured explanation of one submitted model item omitted during generation. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class ModelGenerationIssueDto {
    private String issueType;
    private String itemLabel;
    private ModelGenerationIssueReasonCode reasonCode;
    private String reason;

    public ModelGenerationIssueReasonCode getReasonCode() {
        return reasonCode != null
                ? reasonCode
                : ModelGenerationIssueReasonCode.UNCLASSIFIED_GENERATION_ISSUE;
    }
}
