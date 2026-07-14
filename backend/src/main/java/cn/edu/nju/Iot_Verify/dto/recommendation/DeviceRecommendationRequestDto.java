package cn.edu.nju.Iot_Verify.dto.recommendation;

import jakarta.validation.constraints.Max;
import jakarta.validation.constraints.Min;
import jakarta.validation.constraints.Size;
import lombok.Data;

@Data
public class DeviceRecommendationRequestDto {
    @Min(1)
    @Max(10)
    private Integer maxRecommendations;
    @Size(max = 20, message = "Language must be at most 20 characters")
    private String language;
    @Size(max = RecommendationLimits.MAX_USER_REQUIREMENT_LENGTH,
            message = "User requirement must be at most 2000 characters")
    private String userRequirement;
}
