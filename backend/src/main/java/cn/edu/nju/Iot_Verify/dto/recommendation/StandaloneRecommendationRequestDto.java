package cn.edu.nju.Iot_Verify.dto.recommendation;

import jakarta.validation.constraints.Max;
import jakarta.validation.constraints.Min;
import jakarta.validation.constraints.NotBlank;
import jakarta.validation.constraints.NotNull;
import jakarta.validation.constraints.Pattern;
import jakarta.validation.constraints.Size;
import lombok.Data;

@Data
public class StandaloneRecommendationRequestDto {
    @Min(1)
    @Max(10)
    @NotNull(message = "maxRecommendations is required when specified")
    private Integer maxRecommendations = 5;

    @NotNull(message = "category cannot be null")
    @Size(max = 100, message = "Category must be at most 100 characters")
    private String category = "all";

    @NotNull(message = "language cannot be null")
    @Size(max = 20, message = "Language must be at most 20 characters")
    private String language = "en";

    @NotNull(message = "userRequirement cannot be null")
    @Size(max = RecommendationLimits.MAX_USER_REQUIREMENT_LENGTH,
            message = "User requirement must be at most 2000 characters")
    private String userRequirement = "";

    @NotBlank(message = "requestId is required")
    @Size(min = 8, max = 80, message = "requestId must contain 8-80 characters")
    @Pattern(regexp = "^[A-Za-z0-9_-]+$", message = "requestId must be URL-safe")
    private String requestId;
}
