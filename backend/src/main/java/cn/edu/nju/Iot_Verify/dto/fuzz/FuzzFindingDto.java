package cn.edu.nju.Iot_Verify.dto.fuzz;

import cn.edu.nju.Iot_Verify.dto.spec.SpecificationDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class FuzzFindingDto {
    private Long id;
    private Long fuzzTaskId;
    private String violatedSpecId;
    private SpecificationDto violatedSpec;
    private int firstViolationStep;
    @Builder.Default
    private List<TraceStateDto> states = new ArrayList<>();
    private Long seed;
    @Builder.Default
    private List<FuzzInputEventDto> inputEvents = new ArrayList<>();
    private LocalDateTime createdAt;
}
