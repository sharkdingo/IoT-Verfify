package cn.edu.nju.Iot_Verify.dto.trace;

import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import com.fasterxml.jackson.annotation.JsonInclude;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;

/** Lightweight counterexample evidence for run-history lists. */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class TraceSummaryDto {
    private Long id;
    private Long verificationTaskId;
    private String violatedSpecId;
    private SpecificationDto violatedSpec;
    private Integer stateCount;
    private LocalDateTime createdAt;
    @Builder.Default
    private Boolean dataAvailable = true;
    private String unavailableReasonCode;
}
