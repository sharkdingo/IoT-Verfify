package cn.edu.nju.Iot_Verify.dto.recommendation;

import com.fasterxml.jackson.annotation.JsonInclude;
import lombok.Data;

import java.util.List;

@Data
@JsonInclude(JsonInclude.Include.NON_NULL)
public class RuleRecommendationDto {
    private String category;
    /** User-facing rule name that is persisted when the recommendation is applied. */
    private String name;
    private List<ConditionDto> conditions;
    private CommandDto command;

    @Data
    @JsonInclude(JsonInclude.Include.NON_NULL)
    public static class ConditionDto {
        private String deviceId;
        private String deviceLabel;
        private String deviceName;
        private String attribute;
        private String targetType;
        private String relation;
        private String value;
    }

    @Data
    @JsonInclude(JsonInclude.Include.NON_NULL)
    public static class CommandDto {
        private String deviceId;
        private String deviceLabel;
        private String deviceName;
        private String action;
        private String contentDevice;
        private String contentDeviceLabel;
        private String content;
        private String contentPrivacy;
    }
}
