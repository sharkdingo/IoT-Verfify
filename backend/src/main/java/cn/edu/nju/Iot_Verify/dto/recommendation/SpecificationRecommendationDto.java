package cn.edu.nju.Iot_Verify.dto.recommendation;

import com.fasterxml.jackson.annotation.JsonInclude;
import com.fasterxml.jackson.annotation.JsonProperty;
import lombok.Data;

import java.util.List;

@Data
@JsonInclude(JsonInclude.Include.NON_NULL)
public class SpecificationRecommendationDto {
    private String category;
    /** Advisory explanation only; the persisted specification is templateId plus conditions. */
    private String rationale;
    private String templateId;
    @JsonProperty("aConditions")
    private List<ConditionDto> aConditions;
    private List<ConditionDto> ifConditions;
    private List<ConditionDto> thenConditions;

    /** Exact authored condition shape; persistence-only id/side fields do not belong in a recommendation. */
    @Data
    @JsonInclude(JsonInclude.Include.NON_NULL)
    public static class ConditionDto {
        private String deviceId;
        private String deviceLabel;
        private String targetType;
        private String key;
        private String propertyScope;
        private String relation;
        private String value;
    }
}
