package cn.edu.nju.Iot_Verify.dto.recommendation;

import lombok.Data;

@Data
public class RecommendationFilterItemDto {
    private String type;
    private Integer index;
    private String reasonCode;
    private String reason;
    private String label;
}
