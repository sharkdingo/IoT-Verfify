package cn.edu.nju.Iot_Verify.dto.rule;

import com.fasterxml.jackson.annotation.JsonGetter;
import lombok.Builder;
import lombok.Data;

@Data
@Builder
public class RuleSimilarityResultDto {
    private boolean isSimilar;
    private boolean isDuplicate;
    private boolean requiresReview;
    private String matchedRule;
    private double similarity;
    private String reasonCode;
    private String reason;
    private String message;

    @JsonGetter("isSimilar")
    public boolean isSimilar() {
        return isSimilar;
    }

    @JsonGetter("isDuplicate")
    public boolean isDuplicate() {
        return isDuplicate;
    }
}
