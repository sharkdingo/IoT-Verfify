package cn.edu.nju.Iot_Verify.dto.fuzz;

import jakarta.validation.constraints.Max;
import jakarta.validation.constraints.Min;
import jakarta.validation.constraints.NotNull;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FuzzPaperDomainPreviewRequestDto {

    @NotNull(message = "Path length cannot be null")
    @Min(value = 1, message = "Path length must be at least 1")
    @Max(value = 50, message = "Path length must be at most 50")
    @Builder.Default
    private Integer pathLength = 20;
}
