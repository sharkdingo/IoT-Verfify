package cn.edu.nju.Iot_Verify.util.mapper;

import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceDto;
import cn.edu.nju.Iot_Verify.dto.simulation.SimulationTraceSummaryDto;
import cn.edu.nju.Iot_Verify.dto.trace.TraceStateDto;
import cn.edu.nju.Iot_Verify.po.SimulationTracePo;
import cn.edu.nju.Iot_Verify.util.JsonUtils;
import com.fasterxml.jackson.core.type.TypeReference;
import org.springframework.stereotype.Component;

import java.util.List;

/**
 * SimulationTrace PO 与 DTO 之间的转换映射器
 */
@Component
public class SimulationTraceMapper {

    /**
     * SimulationTracePo -> SimulationTraceDto（详情）
     */
    public SimulationTraceDto toDto(SimulationTracePo po) {
        if (po == null) return null;

        return SimulationTraceDto.builder()
                .id(po.getId())
                .userId(po.getUserId())
                .requestedSteps(po.getRequestedSteps())
                .steps(po.getSteps())
                .states(JsonUtils.fromJsonOrDefault(
                        po.getStatesJson(),
                        new TypeReference<List<TraceStateDto>>() {},
                        List.of()))
                .logs(JsonUtils.fromJsonToStringList(po.getLogsJson()))
                .nusmvOutput(po.getNusmvOutput())
                .requestJson(po.getRequestJson())
                .createdAt(po.getCreatedAt())
                .build();
    }

    /**
     * SimulationTracePo -> SimulationTraceSummaryDto（列表摘要）
     */
    public SimulationTraceSummaryDto toSummaryDto(SimulationTracePo po) {
        if (po == null) return null;

        return SimulationTraceSummaryDto.builder()
                .id(po.getId())
                .requestedSteps(po.getRequestedSteps())
                .steps(po.getSteps())
                .createdAt(po.getCreatedAt())
                .build();
    }

    /**
     * List<SimulationTracePo> -> List<SimulationTraceSummaryDto>
     */
    public List<SimulationTraceSummaryDto> toSummaryDtoList(List<SimulationTracePo> poList) {
        return poList.stream().map(this::toSummaryDto).toList();
    }
}
