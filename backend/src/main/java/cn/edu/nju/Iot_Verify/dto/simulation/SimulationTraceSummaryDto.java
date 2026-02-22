package cn.edu.nju.Iot_Verify.dto.simulation;

import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;

/**
 * 模拟轨迹摘要 DTO（列表接口用，不含大 JSON 字段）
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class SimulationTraceSummaryDto {

    private Long id;

    private int requestedSteps;

    private int steps;

    private LocalDateTime createdAt;
}
