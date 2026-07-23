package cn.edu.nju.Iot_Verify.dto.fuzz;

import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
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
public class FuzzFindingSummaryDto {
    private Long id;
    private Long fuzzTaskId;
    private String violatedSpecId;
    private SpecificationDto violatedSpec;
    private String specificationLabel;
    private int firstViolationStep;
    private Long seed;
    private LocalDateTime createdAt;
    private int stateCount;
}
