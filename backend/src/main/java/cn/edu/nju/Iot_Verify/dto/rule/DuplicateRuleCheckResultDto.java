package cn.edu.nju.Iot_Verify.dto.rule;

import com.fasterxml.jackson.annotation.JsonGetter;
import lombok.Builder;
import lombok.Data;

@Data
@Builder
public class DuplicateRuleCheckResultDto {
    private boolean isDuplicate;
    private boolean requiresReview;
    private String matchedRule;
    private double similarity;
    private String matchType;
    private String reasonCode;
    private String reason;
    private String message;

    @JsonGetter("isDuplicate")
    public boolean isDuplicate() {
        return isDuplicate;
    }
}
