package cn.edu.nju.Iot_Verify.dto.recommendation;

import com.fasterxml.jackson.annotation.JsonInclude;
import lombok.Data;

import java.util.List;

@Data
@JsonInclude(JsonInclude.Include.NON_NULL)
public class RecommendationResponseDto<T> {
    private String message;
    private Integer count;
    private Integer requestedCount;
    private Integer validatedCount;
    private Integer filteredCount;
    private List<RecommendationFilterItemDto> filteredItems;
    private Integer adjustedCount;
    private List<RecommendationAdjustmentItemDto> adjustedItems;
    private Integer rawCandidateCount;
    private Integer inspectedCount;
    private Integer truncatedCount;
    private List<T> recommendations;
}
