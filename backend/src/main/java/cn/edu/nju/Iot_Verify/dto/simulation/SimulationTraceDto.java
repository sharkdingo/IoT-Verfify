package cn.edu.nju.Iot_Verify.dto.simulation;

import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import com.fasterxml.jackson.annotation.JsonInclude;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.time.LocalDateTime;
import java.util.List;

/**
 * 模拟轨迹详情 DTO（含完整 states/logs）
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
@JsonInclude(JsonInclude.Include.NON_NULL)
public class SimulationTraceDto {

    private Long id;

    private Long userId;

    private int requestedSteps;

    private int steps;

    /** 模拟轨迹状态列表 */
    private List<TraceStateDto> states;

    /** 执行日志 */
    private List<String> logs;

    /** NuSMV 原始输出（截断） */
    private String nusmvOutput;

    /** 请求快照 JSON */
    private String requestJson;

    private LocalDateTime createdAt;
}
