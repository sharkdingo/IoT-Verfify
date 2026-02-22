package cn.edu.nju.Iot_Verify.dto.simulation;

import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import lombok.AllArgsConstructor;
import lombok.Builder;
import lombok.Data;
import lombok.NoArgsConstructor;

import java.util.List;

/**
 * 模拟结果 DTO
 */
@Data
@Builder
@NoArgsConstructor
@AllArgsConstructor
public class SimulationResultDto {

    /** 模拟轨迹状态列表（初始状态 + N 步） */
    private List<TraceStateDto> states;

    /** 实际模拟步数（states.size() - 1，不含初始状态） */
    private int steps;

    /** 用户请求的模拟步数 */
    private int requestedSteps;

    /** NuSMV 原始输出（截断） */
    private String nusmvOutput;

    /** 执行日志 */
    private List<String> logs;
}
