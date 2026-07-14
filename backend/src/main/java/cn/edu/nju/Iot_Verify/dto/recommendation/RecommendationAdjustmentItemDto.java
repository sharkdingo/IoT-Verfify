package cn.edu.nju.Iot_Verify.dto.recommendation;

import lombok.Data;

import java.util.Map;

@Data
public class RecommendationAdjustmentItemDto {
    private String type;
    private Integer index;
    private String reasonCode;
    private String reason;
    private String label;
    private Map<String, Object> appliedValues;
}
