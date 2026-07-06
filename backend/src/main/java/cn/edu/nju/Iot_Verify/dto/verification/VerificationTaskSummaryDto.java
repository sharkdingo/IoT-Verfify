package cn.edu.nju.Iot_Verify.dto.verification;

import com.fasterxml.jackson.annotation.JsonInclude;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class VerificationTaskSummaryDto {

    private Long id;
    private String status;
    private LocalDateTime createdAt;
    private LocalDateTime startedAt;
    private LocalDateTime completedAt;
    private Long processingTimeMs;
    private Integer progress;
    private Boolean isSafe;
    private Integer violatedSpecCount;
    private Integer disabledRuleCount;
    private Integer skippedSpecCount;
    private String errorMessage;
}
